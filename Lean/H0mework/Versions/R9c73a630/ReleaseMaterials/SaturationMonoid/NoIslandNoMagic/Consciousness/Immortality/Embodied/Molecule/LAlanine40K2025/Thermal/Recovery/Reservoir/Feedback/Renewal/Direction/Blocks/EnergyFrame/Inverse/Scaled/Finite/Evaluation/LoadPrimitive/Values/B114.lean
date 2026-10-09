import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B076

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1825_pa : Scalar.QComplex := ((999998715175218158126217621270 : Int)/10^30,(-1603012137480258609703918123 : Int)/10^30)
theorem v1825_pa_checked : Scalar.distance (sourceCoefficient 20 96 1 0) v1825_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1825_pb : Scalar.QComplex := ((-691663479862314731843623 : Int)/10^30,(-431476827295359803353448305 : Int)/10^30)
theorem v1825_pb_checked : Scalar.distance (sourceCoefficient 20 96 1 1) v1825_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1825_pg : Scalar.QComplex := ((-93086295267536211426340 : Int)/10^30,(149218652866754820018 : Int)/10^30)
theorem v1825_pg_checked : Scalar.distance (sourceCoefficient 20 96 1 2) v1825_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1825_mb : Scalar.QComplex := ((-1064008291285371404078509 : Int)/10^30,(-431476069762385781684546445 : Int)/10^30)
theorem v1825_mb_checked : Scalar.distance (sourceCoefficient 20 96 3 1) v1825_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1825_mg : Scalar.QComplex := ((-93086131838277364101323 : Int)/10^30,(229547877670606729646 : Int)/10^30)
theorem v1825_mg_checked : Scalar.distance (sourceCoefficient 20 96 3 2) v1825_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1825_upper : Scalar.QComplex := ((999994459141074839602196719014 : Int)/10^30,(-3328916813199628014538087406 : Int)/10^30)
theorem v1825_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 96 5) 1) 14) v1825_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1825 : Material (20 : Basis) (96 : Basis) where
  plus := ![v1825_pa,v1825_pb,v1825_pg]
  minus := ![(Primitive.Addresses.material1825 1).one,v1825_mb,v1825_mg]
  upper := v1825_upper
  lower := (Primitive.Addresses.material1825 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1825_pa_checked.trans (by decide +kernel)
    · exact v1825_pb_checked.trans (by decide +kernel)
    · exact v1825_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 96 Primitive.Addresses.material1825
    · exact v1825_mb_checked.trans (by decide +kernel)
    · exact v1825_mg_checked.trans (by decide +kernel)
  upper_error := v1825_upper_checked
  lower_error := reuse_lower_error 20 96 Primitive.Addresses.material1825

def v1826_pa : Scalar.QComplex := ((999998595218934284183860380160 : Int)/10^30,(-1676174262426729211223694891 : Int)/10^30)
theorem v1826_pa_checked : Scalar.distance (sourceCoefficient 20 97 1 0) v1826_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1826_pb : Scalar.QComplex := ((-723231256775493222349622 : Int)/10^30,(-431476760505104231585846370 : Int)/10^30)
theorem v1826_pb_checked : Scalar.distance (sourceCoefficient 20 97 1 1) v1826_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1826_pg : Scalar.QComplex := ((-93086282479761200780387 : Int)/10^30,(156029050064215128387 : Int)/10^30)
theorem v1826_pg_checked : Scalar.distance (sourceCoefficient 20 97 1 2) v1826_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1826_mb : Scalar.QComplex := ((-1095575998807441394140270 : Int)/10^30,(-431475975730585362802483480 : Int)/10^30)
theorem v1826_mb_checked : Scalar.distance (sourceCoefficient 20 97 3 1) v1826_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1826_mg : Scalar.QComplex := ((-93086113173441062423652 : Int)/10^30,(236358261296971016692 : Int)/10^30)
theorem v1826_mg_checked : Scalar.distance (sourceCoefficient 20 97 3 2) v1826_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1826_upper : Scalar.QComplex := ((999994212913779184973413250776 : Int)/10^30,(-3402078622146044117837918266 : Int)/10^30)
theorem v1826_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 97 5) 1) 14) v1826_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1826 : Material (20 : Basis) (97 : Basis) where
  plus := ![v1826_pa,v1826_pb,v1826_pg]
  minus := ![(Primitive.Addresses.material1826 1).one,v1826_mb,v1826_mg]
  upper := v1826_upper
  lower := (Primitive.Addresses.material1826 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1826_pa_checked.trans (by decide +kernel)
    · exact v1826_pb_checked.trans (by decide +kernel)
    · exact v1826_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 97 Primitive.Addresses.material1826
    · exact v1826_mb_checked.trans (by decide +kernel)
    · exact v1826_mg_checked.trans (by decide +kernel)
  upper_error := v1826_upper_checked
  lower_error := reuse_lower_error 20 97 Primitive.Addresses.material1826

def v1827_pa : Scalar.QComplex := ((999999949286029510655948617728 : Int)/10^30,(-318477532028212784520211007 : Int)/10^30)
theorem v1827_pa_checked : Scalar.distance (sourceCoefficient 21 22 1 0) v1827_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1827_pb : Scalar.QComplex := ((-137415896013894704961007 : Int)/10^30,(-431477499118574644184407934 : Int)/10^30)
theorem v1827_pb_checked : Scalar.distance (sourceCoefficient 21 22 1 1) v1827_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1827_pg : Scalar.QComplex := ((-93086425176178515392263 : Int)/10^30,(29645936458901372734 : Int)/10^30)
theorem v1827_pg_checked : Scalar.distance (sourceCoefficient 21 22 1 2) v1827_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1827_mb : Scalar.QComplex := ((-509761493561833823152818 : Int)/10^30,(-431477219876052948686004637 : Int)/10^30)
theorem v1827_mb_checked : Scalar.distance (sourceCoefficient 21 22 3 1) v1827_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1827_mg : Scalar.QComplex := ((-93086364932740201886896 : Int)/10^30,(109975317890447784378 : Int)/10^30)
theorem v1827_mg_checked : Scalar.distance (sourceCoefficient 21 22 3 2) v1827_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1827_upper : Scalar.QComplex := ((999997910240245070170310350348 : Int)/10^30,(-2044386250874287712058589836 : Int)/10^30)
theorem v1827_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 22 5) 1) 14) v1827_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1827 : Material (21 : Basis) (22 : Basis) where
  plus := ![v1827_pa,v1827_pb,v1827_pg]
  minus := ![(Primitive.Addresses.material1827 1).one,v1827_mb,v1827_mg]
  upper := v1827_upper
  lower := (Primitive.Addresses.material1827 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1827_pa_checked.trans (by decide +kernel)
    · exact v1827_pb_checked.trans (by decide +kernel)
    · exact v1827_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 22 Primitive.Addresses.material1827
    · exact v1827_mb_checked.trans (by decide +kernel)
    · exact v1827_mg_checked.trans (by decide +kernel)
  upper_error := v1827_upper_checked
  lower_error := reuse_lower_error 21 22 Primitive.Addresses.material1827

def v1828_pa : Scalar.QComplex := ((999999945949790107137797151156 : Int)/10^30,(-328786278400269034456198035 : Int)/10^30)
theorem v1828_pa_checked : Scalar.distance (sourceCoefficient 21 23 1 0) v1828_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1828_pb : Scalar.QComplex := ((-141863888339940320233905 : Int)/10^30,(-431477497669353153056088648 : Int)/10^30)
theorem v1828_pb_checked : Scalar.distance (sourceCoefficient 21 23 1 1) v1828_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1828_pg : Scalar.QComplex := ((-93086424864572576355276 : Int)/10^30,(30605540855044991942 : Int)/10^30)
theorem v1828_pg_checked : Scalar.distance (sourceCoefficient 21 23 1 2) v1828_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1828_mb : Scalar.QComplex := ((-514209482981075735816501 : Int)/10^30,(-431477214588414949929474031 : Int)/10^30)
theorem v1828_mb_checked : Scalar.distance (sourceCoefficient 21 23 3 1) v1828_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1828_mg : Scalar.QComplex := ((-93086363793039003980736 : Int)/10^30,(110934921660384939635 : Int)/10^30)
theorem v1828_mg_checked : Scalar.distance (sourceCoefficient 21 23 3 2) v1828_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1828_upper : Scalar.QComplex := ((999997889112049599585235359402 : Int)/10^30,(-2054694976134630642032378914 : Int)/10^30)
theorem v1828_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 23 5) 1) 14) v1828_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1828 : Material (21 : Basis) (23 : Basis) where
  plus := ![v1828_pa,v1828_pb,v1828_pg]
  minus := ![(Primitive.Addresses.material1828 1).one,v1828_mb,v1828_mg]
  upper := v1828_upper
  lower := (Primitive.Addresses.material1828 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1828_pa_checked.trans (by decide +kernel)
    · exact v1828_pb_checked.trans (by decide +kernel)
    · exact v1828_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 23 Primitive.Addresses.material1828
    · exact v1828_mb_checked.trans (by decide +kernel)
    · exact v1828_mg_checked.trans (by decide +kernel)
  upper_error := v1828_upper_checked
  lower_error := reuse_lower_error 21 23 Primitive.Addresses.material1828

def v1829_pa : Scalar.QComplex := ((999999927901705963169286470453 : Int)/10^30,(-379732251560882597674336170 : Int)/10^30)
theorem v1829_pa_checked : Scalar.distance (sourceCoefficient 21 24 1 0) v1829_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1829_pb : Scalar.QComplex := ((-163845930440306716244720 : Int)/10^30,(-431477489609610302526384169 : Int)/10^30)
theorem v1829_pb_checked : Scalar.distance (sourceCoefficient 21 24 1 1) v1829_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1829_pg : Scalar.QComplex := ((-93086423155157210178713 : Int)/10^30,(35347919602981625634 : Int)/10^30)
theorem v1829_pg_checked : Scalar.distance (sourceCoefficient 21 24 1 2) v1829_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1829_mb : Scalar.QComplex := ((-536191509941328146243000 : Int)/10^30,(-431477187559162802218576627 : Int)/10^30)
theorem v1829_mb_checked : Scalar.distance (sourceCoefficient 21 24 3 1) v1829_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1829_mg : Scalar.QComplex := ((-93086357991165003638341 : Int)/10^30,(115677297167368756254 : Int)/10^30)
theorem v1829_mg_checked : Scalar.distance (sourceCoefficient 21 24 3 2) v1829_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1829_upper : Scalar.QComplex := ((999997783135864443480716743954 : Int)/10^30,(-2105640842267845793828605260 : Int)/10^30)
theorem v1829_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 24 5) 1) 14) v1829_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1829 : Material (21 : Basis) (24 : Basis) where
  plus := ![v1829_pa,v1829_pb,v1829_pg]
  minus := ![(Primitive.Addresses.material1829 1).one,v1829_mb,v1829_mg]
  upper := v1829_upper
  lower := (Primitive.Addresses.material1829 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1829_pa_checked.trans (by decide +kernel)
    · exact v1829_pb_checked.trans (by decide +kernel)
    · exact v1829_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 24 Primitive.Addresses.material1829
    · exact v1829_mb_checked.trans (by decide +kernel)
    · exact v1829_mg_checked.trans (by decide +kernel)
  upper_error := v1829_upper_checked
  lower_error := reuse_lower_error 21 24 Primitive.Addresses.material1829

def v1830_pa : Scalar.QComplex := ((999999918909671219569930957298 : Int)/10^30,(-402716588912374848009404358 : Int)/10^30)
theorem v1830_pa_checked : Scalar.distance (sourceCoefficient 21 25 1 0) v1830_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1830_pb : Scalar.QComplex := ((-173763155237381783935897 : Int)/10^30,(-431477485484658482886118937 : Int)/10^30)
theorem v1830_pb_checked : Scalar.distance (sourceCoefficient 21 25 1 1) v1830_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1830_pg : Scalar.QComplex := ((-93086422291682987468173 : Int)/10^30,(37487449499233028914 : Int)/10^30)
theorem v1830_pg_checked : Scalar.distance (sourceCoefficient 21 25 1 2) v1830_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1830_mb : Scalar.QComplex := ((-546108727486119543003310 : Int)/10^30,(-431477174876094173834849000 : Int)/10^30)
theorem v1830_mb_checked : Scalar.distance (sourceCoefficient 21 25 3 1) v1830_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1830_mg : Scalar.QComplex := ((-93086355281373162823201 : Int)/10^30,(117816825521836033049 : Int)/10^30)
theorem v1830_mg_checked : Scalar.distance (sourceCoefficient 21 25 3 2) v1830_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1830_upper : Scalar.QComplex := ((999997734474961946581651098273 : Int)/10^30,(-2128625129867431272608160218 : Int)/10^30)
theorem v1830_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 25 5) 1) 14) v1830_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1830 : Material (21 : Basis) (25 : Basis) where
  plus := ![v1830_pa,v1830_pb,v1830_pg]
  minus := ![(Primitive.Addresses.material1830 1).one,v1830_mb,v1830_mg]
  upper := v1830_upper
  lower := (Primitive.Addresses.material1830 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1830_pa_checked.trans (by decide +kernel)
    · exact v1830_pb_checked.trans (by decide +kernel)
    · exact v1830_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 25 Primitive.Addresses.material1830
    · exact v1830_mb_checked.trans (by decide +kernel)
    · exact v1830_mg_checked.trans (by decide +kernel)
  upper_error := v1830_upper_checked
  lower_error := reuse_lower_error 21 25 Primitive.Addresses.material1830

def v1831_pa : Scalar.QComplex := ((999999915925181772302497512545 : Int)/10^30,(-410060519175913770332505116 : Int)/10^30)
theorem v1831_pa_checked : Scalar.distance (sourceCoefficient 21 26 1 0) v1831_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1831_pb : Scalar.QComplex := ((-176931896019342176991702 : Int)/10^30,(-431477484102590109245710471 : Int)/10^30)
theorem v1831_pb_checked : Scalar.distance (sourceCoefficient 21 26 1 1) v1831_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1831_pg : Scalar.QComplex := ((-93086422003692387837780 : Int)/10^30,(38171069744288054242 : Int)/10^30)
theorem v1831_pg_checked : Scalar.distance (sourceCoefficient 21 26 1 2) v1831_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1831_mb : Scalar.QComplex := ((-549277465895550163924535 : Int)/10^30,(-431477170759545734756838054 : Int)/10^30)
theorem v1831_mb_checked : Scalar.distance (sourceCoefficient 21 26 3 1) v1831_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1831_mg : Scalar.QComplex := ((-93086354403449188055275 : Int)/10^30,(118500445263825081289 : Int)/10^30)
theorem v1831_mg_checked : Scalar.distance (sourceCoefficient 21 26 3 2) v1831_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1831_upper : Scalar.QComplex := ((999997718815519545641643731358 : Int)/10^30,(-2135969044042090710822738363 : Int)/10^30)
theorem v1831_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 26 5) 1) 14) v1831_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1831 : Material (21 : Basis) (26 : Basis) where
  plus := ![v1831_pa,v1831_pb,v1831_pg]
  minus := ![(Primitive.Addresses.material1831 1).one,v1831_mb,v1831_mg]
  upper := v1831_upper
  lower := (Primitive.Addresses.material1831 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1831_pa_checked.trans (by decide +kernel)
    · exact v1831_pb_checked.trans (by decide +kernel)
    · exact v1831_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 26 Primitive.Addresses.material1831
    · exact v1831_mb_checked.trans (by decide +kernel)
    · exact v1831_mg_checked.trans (by decide +kernel)
  upper_error := v1831_upper_checked
  lower_error := reuse_lower_error 21 26 Primitive.Addresses.material1831

def v1832_pa : Scalar.QComplex := ((999999913843603522619404839868 : Int)/10^30,(-415105752226871142345908391 : Int)/10^30)
theorem v1832_pa_checked : Scalar.distance (sourceCoefficient 21 27 1 0) v1832_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1832_pb : Scalar.QComplex := ((-179108800637137393337193 : Int)/10^30,(-431477483135137967349725512 : Int)/10^30)
theorem v1832_pb_checked : Scalar.distance (sourceCoefficient 21 27 1 1) v1832_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1832_pg : Scalar.QComplex := ((-93086421802450576172801 : Int)/10^30,(38640712473558608757 : Int)/10^30)
theorem v1832_pg_checked : Scalar.distance (sourceCoefficient 21 27 1 2) v1832_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1832_mb : Scalar.QComplex := ((-551454368867916675579706 : Int)/10^30,(-431477167913523312074644341 : Int)/10^30)
theorem v1832_mb_checked : Scalar.distance (sourceCoefficient 21 27 3 1) v1832_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1832_mg : Scalar.QComplex := ((-93086353796926927884660 : Int)/10^30,(118970087644563564091 : Int)/10^30)
theorem v1832_mg_checked : Scalar.distance (sourceCoefficient 21 27 3 2) v1832_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1832_upper : Scalar.QComplex := ((999997708026329850239437428914 : Int)/10^30,(-2141014265986150888491685519 : Int)/10^30)
theorem v1832_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 27 5) 1) 14) v1832_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1832 : Material (21 : Basis) (27 : Basis) where
  plus := ![v1832_pa,v1832_pb,v1832_pg]
  minus := ![(Primitive.Addresses.material1832 1).one,v1832_mb,v1832_mg]
  upper := v1832_upper
  lower := (Primitive.Addresses.material1832 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1832_pa_checked.trans (by decide +kernel)
    · exact v1832_pb_checked.trans (by decide +kernel)
    · exact v1832_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 27 Primitive.Addresses.material1832
    · exact v1832_mb_checked.trans (by decide +kernel)
    · exact v1832_mg_checked.trans (by decide +kernel)
  upper_error := v1832_upper_checked
  lower_error := reuse_lower_error 21 27 Primitive.Addresses.material1832

def v1833_pa : Scalar.QComplex := ((999999910999205400591148726331 : Int)/10^30,(-421902336184188796702051332 : Int)/10^30)
theorem v1833_pa_checked : Scalar.distance (sourceCoefficient 21 28 1 0) v1833_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1833_pb : Scalar.QComplex := ((-182041373787789531919104 : Int)/10^30,(-431477481808702990114425200 : Int)/10^30)
theorem v1833_pb_checked : Scalar.distance (sourceCoefficient 21 28 1 1) v1833_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1833_pg : Scalar.QComplex := ((-93086421526981417480048 : Int)/10^30,(39273382204621845851 : Int)/10^30)
theorem v1833_pg_checked : Scalar.distance (sourceCoefficient 21 28 1 2) v1833_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1833_mb : Scalar.QComplex := ((-554386939781984160019503 : Int)/10^30,(-431477164056410277910643959 : Int)/10^30)
theorem v1833_mb_checked : Scalar.distance (sourceCoefficient 21 28 3 1) v1833_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1833_mg : Scalar.QComplex := ((-93086352975492388241017 : Int)/10^30,(119602756902337468594 : Int)/10^30)
theorem v1833_mg_checked : Scalar.distance (sourceCoefficient 21 28 3 2) v1833_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1833_upper : Scalar.QComplex := ((999997693451648635557925400450 : Int)/10^30,(-2147810834911582004419292685 : Int)/10^30)
theorem v1833_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 28 5) 1) 14) v1833_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1833 : Material (21 : Basis) (28 : Basis) where
  plus := ![v1833_pa,v1833_pb,v1833_pg]
  minus := ![(Primitive.Addresses.material1833 1).one,v1833_mb,v1833_mg]
  upper := v1833_upper
  lower := (Primitive.Addresses.material1833 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1833_pa_checked.trans (by decide +kernel)
    · exact v1833_pb_checked.trans (by decide +kernel)
    · exact v1833_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 28 Primitive.Addresses.material1833
    · exact v1833_mb_checked.trans (by decide +kernel)
    · exact v1833_mg_checked.trans (by decide +kernel)
  upper_error := v1833_upper_checked
  lower_error := reuse_lower_error 21 28 Primitive.Addresses.material1833

def v1834_pa : Scalar.QComplex := ((999999905096826536964725628979 : Int)/10^30,(-435667692076722869986412847 : Int)/10^30)
theorem v1834_pa_checked : Scalar.distance (sourceCoefficient 21 29 1 0) v1834_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1834_pb : Scalar.QComplex := ((-187980815316768546193531 : Int)/10^30,(-431477479040810838773268067 : Int)/10^30)
theorem v1834_pb_checked : Scalar.distance (sourceCoefficient 21 29 1 1) v1834_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1834_pg : Scalar.QComplex := ((-93086420953694904674063 : Int)/10^30,(40554750029353032150 : Int)/10^30)
theorem v1834_pg_checked : Scalar.distance (sourceCoefficient 21 29 1 2) v1834_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1834_mb : Scalar.QComplex := ((-560326376710871381794905 : Int)/10^30,(-431477156163048620189649410 : Int)/10^30)
theorem v1834_mb_checked : Scalar.distance (sourceCoefficient 21 29 3 1) v1834_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1834_mg : Scalar.QComplex := ((-93086351296443366817292 : Int)/10^30,(120884123755236411657 : Int)/10^30)
theorem v1834_mg_checked : Scalar.distance (sourceCoefficient 21 29 3 2) v1834_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1834_upper : Scalar.QComplex := ((999997663791523075649277700997 : Int)/10^30,(-2161576160115265009073323138 : Int)/10^30)
theorem v1834_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 29 5) 1) 14) v1834_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1834 : Material (21 : Basis) (29 : Basis) where
  plus := ![v1834_pa,v1834_pb,v1834_pg]
  minus := ![(Primitive.Addresses.material1834 1).one,v1834_mb,v1834_mg]
  upper := v1834_upper
  lower := (Primitive.Addresses.material1834 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1834_pa_checked.trans (by decide +kernel)
    · exact v1834_pb_checked.trans (by decide +kernel)
    · exact v1834_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 29 Primitive.Addresses.material1834
    · exact v1834_mb_checked.trans (by decide +kernel)
    · exact v1834_mg_checked.trans (by decide +kernel)
  upper_error := v1834_upper_checked
  lower_error := reuse_lower_error 21 29 Primitive.Addresses.material1834

def v1835_pa : Scalar.QComplex := ((999999902810649315790973515211 : Int)/10^30,(-440883989188367064420583086 : Int)/10^30)
theorem v1835_pa_checked : Scalar.distance (sourceCoefficient 21 30 1 0) v1835_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1835_pb : Scalar.QComplex := ((-190231530217942052134456 : Int)/10^30,(-431477477963453566696900668 : Int)/10^30)
theorem v1835_pb_checked : Scalar.distance (sourceCoefficient 21 30 1 1) v1835_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1835_pg : Scalar.QComplex := ((-93086420731075000289278 : Int)/10^30,(41040316499864770693 : Int)/10^30)
theorem v1835_pg_checked : Scalar.distance (sourceCoefficient 21 30 1 2) v1835_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1835_mb : Scalar.QComplex := ((-562577089844290063844822 : Int)/10^30,(-431477153143426157986072062 : Int)/10^30)
theorem v1835_mb_checked : Scalar.distance (sourceCoefficient 21 30 3 1) v1835_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1835_mg : Scalar.QComplex := ((-93086350654801550374455 : Int)/10^30,(121369689852838610688 : Int)/10^30)
theorem v1835_mg_checked : Scalar.distance (sourceCoefficient 21 30 3 2) v1835_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1835_upper : Scalar.QComplex := ((999997652502493663547449825785 : Int)/10^30,(-2166792445512112921646976213 : Int)/10^30)
theorem v1835_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 30 5) 1) 14) v1835_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1835 : Material (21 : Basis) (30 : Basis) where
  plus := ![v1835_pa,v1835_pb,v1835_pg]
  minus := ![(Primitive.Addresses.material1835 1).one,v1835_mb,v1835_mg]
  upper := v1835_upper
  lower := (Primitive.Addresses.material1835 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1835_pa_checked.trans (by decide +kernel)
    · exact v1835_pb_checked.trans (by decide +kernel)
    · exact v1835_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 30 Primitive.Addresses.material1835
    · exact v1835_mb_checked.trans (by decide +kernel)
    · exact v1835_mg_checked.trans (by decide +kernel)
  upper_error := v1835_upper_checked
  lower_error := reuse_lower_error 21 30 Primitive.Addresses.material1835

def v1836_pa : Scalar.QComplex := ((999999897857460541995560391360 : Int)/10^30,(-451979057571156179655761270 : Int)/10^30)
theorem v1836_pa_checked : Scalar.distance (sourceCoefficient 21 31 1 0) v1836_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1836_pb : Scalar.QComplex := ((-195018802713559671979664 : Int)/10^30,(-431477475619855754012433603 : Int)/10^30)
theorem v1836_pb_checked : Scalar.distance (sourceCoefficient 21 31 1 1) v1836_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1836_pg : Scalar.QComplex := ((-93086420247735215328748 : Int)/10^30,(42073116793698945398 : Int)/10^30)
theorem v1836_pg_checked : Scalar.distance (sourceCoefficient 21 31 1 2) v1836_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1836_mb : Scalar.QComplex := ((-567364358534967983790661 : Int)/10^30,(-431477146668628664961527822 : Int)/10^30)
theorem v1836_mb_checked : Scalar.distance (sourceCoefficient 21 31 3 1) v1836_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1836_mg : Scalar.QComplex := ((-93086349280201807403018 : Int)/10^30,(122402489345013569089 : Int)/10^30)
theorem v1836_mg_checked : Scalar.distance (sourceCoefficient 21 31 3 2) v1836_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1836_upper : Scalar.QComplex := ((999997628400230774991913044818 : Int)/10^30,(-2177887488821346525207673619 : Int)/10^30)
theorem v1836_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 31 5) 1) 14) v1836_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1836 : Material (21 : Basis) (31 : Basis) where
  plus := ![v1836_pa,v1836_pb,v1836_pg]
  minus := ![(Primitive.Addresses.material1836 1).one,v1836_mb,v1836_mg]
  upper := v1836_upper
  lower := (Primitive.Addresses.material1836 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1836_pa_checked.trans (by decide +kernel)
    · exact v1836_pb_checked.trans (by decide +kernel)
    · exact v1836_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 31 Primitive.Addresses.material1836
    · exact v1836_mb_checked.trans (by decide +kernel)
    · exact v1836_mg_checked.trans (by decide +kernel)
  upper_error := v1836_upper_checked
  lower_error := reuse_lower_error 21 31 Primitive.Addresses.material1836

def v1837_pa : Scalar.QComplex := ((999999895687362337688204961660 : Int)/10^30,(-456755147145051025540923497 : Int)/10^30)
theorem v1837_pa_checked : Scalar.distance (sourceCoefficient 21 32 1 0) v1837_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1837_pb : Scalar.QComplex := ((-197079577953657291758696 : Int)/10^30,(-431477474589203558226217722 : Int)/10^30)
theorem v1837_pb_checked : Scalar.distance (sourceCoefficient 21 32 1 1) v1837_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1837_pg : Scalar.QComplex := ((-93086420035556049447233 : Int)/10^30,(42517705915680480697 : Int)/10^30)
theorem v1837_pg_checked : Scalar.distance (sourceCoefficient 21 32 1 2) v1837_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1837_mb : Scalar.QComplex := ((-569425132118338373488432 : Int)/10^30,(-431477143859620634601382832 : Int)/10^30)
theorem v1837_mb_checked : Scalar.distance (sourceCoefficient 21 32 3 1) v1837_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1837_mg : Scalar.QComplex := ((-93086348684362331806183 : Int)/10^30,(122847078118353191587 : Int)/10^30)
theorem v1837_mg_checked : Scalar.distance (sourceCoefficient 21 32 3 2) v1837_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1837_upper : Scalar.QComplex := ((999997617987038481709930372857 : Int)/10^30,(-2182663567536424358805382273 : Int)/10^30)
theorem v1837_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 32 5) 1) 14) v1837_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1837 : Material (21 : Basis) (32 : Basis) where
  plus := ![v1837_pa,v1837_pb,v1837_pg]
  minus := ![(Primitive.Addresses.material1837 1).one,v1837_mb,v1837_mg]
  upper := v1837_upper
  lower := (Primitive.Addresses.material1837 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1837_pa_checked.trans (by decide +kernel)
    · exact v1837_pb_checked.trans (by decide +kernel)
    · exact v1837_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 32 Primitive.Addresses.material1837
    · exact v1837_mb_checked.trans (by decide +kernel)
    · exact v1837_mg_checked.trans (by decide +kernel)
  upper_error := v1837_upper_checked
  lower_error := reuse_lower_error 21 32 Primitive.Addresses.material1837

def v1838_pa : Scalar.QComplex := ((999999892624994420365738308300 : Int)/10^30,(-463411264029993880506983043 : Int)/10^30)
theorem v1838_pa_checked : Scalar.distance (sourceCoefficient 21 33 1 0) v1838_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1838_pb : Scalar.QComplex := ((-199951542693885697361271 : Int)/10^30,(-431477473130963862756410493 : Int)/10^30)
theorem v1838_pb_checked : Scalar.distance (sourceCoefficient 21 33 1 1) v1838_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1838_pg : Scalar.QComplex := ((-93086419735724181819594 : Int)/10^30,(43137300065626347240 : Int)/10^30)
theorem v1838_pg_checked : Scalar.distance (sourceCoefficient 21 33 1 2) v1838_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1838_mb : Scalar.QComplex := ((-572297094530807870518608 : Int)/10^30,(-431477139923005259774003264 : Int)/10^30)
theorem v1838_mb_checked : Scalar.distance (sourceCoefficient 21 33 3 1) v1838_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1838_mg : Scalar.QComplex := ((-93086347849848729900982 : Int)/10^30,(123466671778854441416 : Int)/10^30)
theorem v1838_mg_checked : Scalar.distance (sourceCoefficient 21 33 3 2) v1838_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1838_upper : Scalar.QComplex := ((999997603436821220220254695546 : Int)/10^30,(-2189319669222493786611312384 : Int)/10^30)
theorem v1838_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 33 5) 1) 14) v1838_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1838 : Material (21 : Basis) (33 : Basis) where
  plus := ![v1838_pa,v1838_pb,v1838_pg]
  minus := ![(Primitive.Addresses.material1838 1).one,v1838_mb,v1838_mg]
  upper := v1838_upper
  lower := (Primitive.Addresses.material1838 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1838_pa_checked.trans (by decide +kernel)
    · exact v1838_pb_checked.trans (by decide +kernel)
    · exact v1838_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 33 Primitive.Addresses.material1838
    · exact v1838_mb_checked.trans (by decide +kernel)
    · exact v1838_mg_checked.trans (by decide +kernel)
  upper_error := v1838_upper_checked
  lower_error := reuse_lower_error 21 33 Primitive.Addresses.material1838

def v1839_pa : Scalar.QComplex := ((999999885002355263017736028534 : Int)/10^30,(-479578227455653195950998412 : Int)/10^30)
theorem v1839_pa_checked : Scalar.distance (sourceCoefficient 21 34 1 0) v1839_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1839_pb : Scalar.QComplex := ((-206927223797815249438511 : Int)/10^30,(-431477469482925030240345896 : Int)/10^30)
theorem v1839_pb_checked : Scalar.distance (sourceCoefficient 21 34 1 1) v1839_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1839_pg : Scalar.QComplex := ((-93086418987430343066702 : Int)/10^30,(44642224951936828816 : Int)/10^30)
theorem v1839_pg_checked : Scalar.distance (sourceCoefficient 21 34 1 2) v1839_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1839_mb : Scalar.QComplex := ((-579272769889279332335662 : Int)/10^30,(-431477130255269165912586670 : Int)/10^30)
theorem v1839_mb_checked : Scalar.distance (sourceCoefficient 21 34 3 1) v1839_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1839_mg : Scalar.QComplex := ((-93086345802872772186933 : Int)/10^30,(124971595459068728414 : Int)/10^30)
theorem v1839_mg_checked : Scalar.distance (sourceCoefficient 21 34 3 2) v1839_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1839_upper : Scalar.QComplex := ((999997567911481198674972789294 : Int)/10^30,(-2205486595413376519304442076 : Int)/10^30)
theorem v1839_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 34 5) 1) 14) v1839_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1839 : Material (21 : Basis) (34 : Basis) where
  plus := ![v1839_pa,v1839_pb,v1839_pg]
  minus := ![(Primitive.Addresses.material1839 1).one,v1839_mb,v1839_mg]
  upper := v1839_upper
  lower := (Primitive.Addresses.material1839 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1839_pa_checked.trans (by decide +kernel)
    · exact v1839_pb_checked.trans (by decide +kernel)
    · exact v1839_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 34 Primitive.Addresses.material1839
    · exact v1839_mb_checked.trans (by decide +kernel)
    · exact v1839_mg_checked.trans (by decide +kernel)
  upper_error := v1839_upper_checked
  lower_error := reuse_lower_error 21 34 Primitive.Addresses.material1839

def v1840_pa : Scalar.QComplex := ((999999859051175716538885665192 : Int)/10^30,(-530940324989872248618067551 : Int)/10^30)
theorem v1840_pa_checked : Scalar.distance (sourceCoefficient 21 35 1 0) v1840_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1840_pb : Scalar.QComplex := ((-229088813479689915449921 : Int)/10^30,(-431477456895482360291346786 : Int)/10^30)
theorem v1840_pb_checked : Scalar.distance (sourceCoefficient 21 35 1 1) v1840_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1840_pg : Scalar.QComplex := ((-93086416421779313545440 : Int)/10^30,(49423339153283635548 : Int)/10^30)
theorem v1840_pg_checked : Scalar.distance (sourceCoefficient 21 35 1 2) v1840_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1840_mb : Scalar.QComplex := ((-601434340456985218308530 : Int)/10^30,(-431477098543377408333211792 : Int)/10^30)
theorem v1840_mb_checked : Scalar.distance (sourceCoefficient 21 35 3 1) v1840_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1840_mg : Scalar.QComplex := ((-93086339111336475602588 : Int)/10^30,(129752705666146924427 : Int)/10^30)
theorem v1840_mg_checked : Scalar.distance (sourceCoefficient 21 35 3 2) v1840_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1840_upper : Scalar.QComplex := ((999997453314019492457561644025 : Int)/10^30,(-2256848571660403085948338016 : Int)/10^30)
theorem v1840_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 35 5) 1) 14) v1840_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1840 : Material (21 : Basis) (35 : Basis) where
  plus := ![v1840_pa,v1840_pb,v1840_pg]
  minus := ![(Primitive.Addresses.material1840 1).one,v1840_mb,v1840_mg]
  upper := v1840_upper
  lower := (Primitive.Addresses.material1840 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1840_pa_checked.trans (by decide +kernel)
    · exact v1840_pb_checked.trans (by decide +kernel)
    · exact v1840_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 35 Primitive.Addresses.material1840
    · exact v1840_mb_checked.trans (by decide +kernel)
    · exact v1840_mg_checked.trans (by decide +kernel)
  upper_error := v1840_upper_checked
  lower_error := reuse_lower_error 21 35 Primitive.Addresses.material1840

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
