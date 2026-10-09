import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B118

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2833_pa : Scalar.QComplex := ((999999161904909562093860722179 : Int)/10^30,(-1294677364625037252927092703 : Int)/10^30)
theorem v2833_pa_checked : Scalar.distance (sourceCoefficient 35 69 1 0) v2833_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2833_pb : Scalar.QComplex := ((-558624151632340883643643 : Int)/10^30,(-431477137637275255342048098 : Int)/10^30)
theorem v2833_pb_checked : Scalar.distance (sourceCoefficient 35 69 1 1) v2833_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2833_pg : Scalar.QComplex := ((-93086349536164261311654 : Int)/10^30,(120516890704660619123 : Int)/10^30)
theorem v2833_pg_checked : Scalar.distance (sourceCoefficient 35 69 1 2) v2833_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2833_mb : Scalar.QComplex := ((-930969280403115407621025 : Int)/10^30,(-431476494911134072747279698 : Int)/10^30)
theorem v2833_mb_checked : Scalar.distance (sourceCoefficient 35 69 3 1) v2833_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2833_mg : Scalar.QComplex := ((-93086210875213273802244 : Int)/10^30,(200846173026872155806 : Int)/10^30)
theorem v2833_mg_checked : Scalar.distance (sourceCoefficient 35 69 3 2) v2833_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2833_upper : Scalar.QComplex := ((999995438027946928194271612595 : Int)/10^30,(-3020583270587751641133054376 : Int)/10^30)
theorem v2833_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 69 5) 1) 14) v2833_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2833 : Material (35 : Basis) (69 : Basis) where
  plus := ![v2833_pa,v2833_pb,v2833_pg]
  minus := ![(Primitive.Addresses.material2833 1).one,v2833_mb,v2833_mg]
  upper := v2833_upper
  lower := (Primitive.Addresses.material2833 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2833_pa_checked.trans (by decide +kernel)
    · exact v2833_pb_checked.trans (by decide +kernel)
    · exact v2833_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 69 Primitive.Addresses.material2833
    · exact v2833_mb_checked.trans (by decide +kernel)
    · exact v2833_mg_checked.trans (by decide +kernel)
  upper_error := v2833_upper_checked
  lower_error := reuse_lower_error 35 69 Primitive.Addresses.material2833

def v2834_pa : Scalar.QComplex := ((999999143377830769855601197776 : Int)/10^30,(-1308909318730196825030590244 : Int)/10^30)
theorem v2834_pa_checked : Scalar.distance (sourceCoefficient 35 70 1 0) v2834_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2834_pb : Scalar.QComplex := ((-564764918106841362656215 : Int)/10^30,(-431477128503128953645824976 : Int)/10^30)
theorem v2834_pb_checked : Scalar.distance (sourceCoefficient 35 70 1 1) v2834_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2834_pg : Scalar.QComplex := ((-93086347688559704052624 : Int)/10^30,(121841692308409682071 : Int)/10^30)
theorem v2834_pg_checked : Scalar.distance (sourceCoefficient 35 70 1 2) v2834_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2834_mb : Scalar.QComplex := ((-937110036708771009599143 : Int)/10^30,(-431476480477786274472518300 : Int)/10^30)
theorem v2834_mb_checked : Scalar.distance (sourceCoefficient 35 70 3 1) v2834_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2834_mg : Scalar.QComplex := ((-93086207884365287304684 : Int)/10^30,(202170972542937515360 : Int)/10^30)
theorem v2834_mg_checked : Scalar.distance (sourceCoefficient 35 70 3 2) v2834_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2834_upper : Scalar.QComplex := ((999995394937834057148908558939 : Int)/10^30,(-3034815171520030144423692758 : Int)/10^30)
theorem v2834_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 70 5) 1) 14) v2834_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2834 : Material (35 : Basis) (70 : Basis) where
  plus := ![v2834_pa,v2834_pb,v2834_pg]
  minus := ![(Primitive.Addresses.material2834 1).one,v2834_mb,v2834_mg]
  upper := v2834_upper
  lower := (Primitive.Addresses.material2834 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2834_pa_checked.trans (by decide +kernel)
    · exact v2834_pb_checked.trans (by decide +kernel)
    · exact v2834_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 70 Primitive.Addresses.material2834
    · exact v2834_mb_checked.trans (by decide +kernel)
    · exact v2834_mg_checked.trans (by decide +kernel)
  upper_error := v2834_upper_checked
  lower_error := reuse_lower_error 35 70 Primitive.Addresses.material2834

def v2835_pa : Scalar.QComplex := ((999999111285666654115353770470 : Int)/10^30,(-1333202114039204109016792843 : Int)/10^30)
theorem v2835_pa_checked : Scalar.distance (sourceCoefficient 35 71 1 0) v2835_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2835_pb : Scalar.QComplex := ((-575246709964740224840736 : Int)/10^30,(-431477112642673317386349765 : Int)/10^30)
theorem v2835_pb_checked : Scalar.distance (sourceCoefficient 35 71 1 1) v2835_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2835_pg : Scalar.QComplex := ((-93086344484029611470819 : Int)/10^30,(124103021546423944289 : Int)/10^30)
theorem v2835_pg_checked : Scalar.distance (sourceCoefficient 35 71 1 2) v2835_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2835_mb : Scalar.QComplex := ((-947591810976960835847692 : Int)/10^30,(-431476455572022252799575078 : Int)/10^30)
theorem v2835_mb_checked : Scalar.distance (sourceCoefficient 35 71 3 1) v2835_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2835_mg : Scalar.QComplex := ((-93086202728411101997740 : Int)/10^30,(204432298173590411192 : Int)/10^30)
theorem v2835_mg_checked : Scalar.distance (sourceCoefficient 35 71 3 2) v2835_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2835_upper : Scalar.QComplex := ((999995320918556860745824577756 : Int)/10^30,(-3059107875259608562455743268 : Int)/10^30)
theorem v2835_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 71 5) 1) 14) v2835_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2835 : Material (35 : Basis) (71 : Basis) where
  plus := ![v2835_pa,v2835_pb,v2835_pg]
  minus := ![(Primitive.Addresses.material2835 1).one,v2835_mb,v2835_mg]
  upper := v2835_upper
  lower := (Primitive.Addresses.material2835 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2835_pa_checked.trans (by decide +kernel)
    · exact v2835_pb_checked.trans (by decide +kernel)
    · exact v2835_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 71 Primitive.Addresses.material2835
    · exact v2835_mb_checked.trans (by decide +kernel)
    · exact v2835_mg_checked.trans (by decide +kernel)
  upper_error := v2835_upper_checked
  lower_error := reuse_lower_error 35 71 Primitive.Addresses.material2835

def v2836_pa : Scalar.QComplex := ((999999075791463993067917266578 : Int)/10^30,(-1359564716316382688946625533 : Int)/10^30)
theorem v2836_pa_checked : Scalar.distance (sourceCoefficient 35 72 1 0) v2836_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2836_pb : Scalar.QComplex := ((-586621576484898224811947 : Int)/10^30,(-431477095046734022535385380 : Int)/10^30)
theorem v2836_pb_checked : Scalar.distance (sourceCoefficient 35 72 1 1) v2836_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2836_pg : Scalar.QComplex := ((-93086340933952151916198 : Int)/10^30,(126557021669878457942 : Int)/10^30)
theorem v2836_pg_checked : Scalar.distance (sourceCoefficient 35 72 1 2) v2836_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2836_mb : Scalar.QComplex := ((-958966658077233053513431 : Int)/10^30,(-431476428160092007795043826 : Int)/10^30)
theorem v2836_mb_checked : Scalar.distance (sourceCoefficient 35 72 3 1) v2836_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2836_mg : Scalar.QComplex := ((-93086197060643381820672 : Int)/10^30,(206886294319751567496 : Int)/10^30)
theorem v2836_mg_checked : Scalar.distance (sourceCoefficient 35 72 3 2) v2836_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2836_upper : Scalar.QComplex := ((999995239924947130330039087575 : Int)/10^30,(-3085470377013014035271907548 : Int)/10^30)
theorem v2836_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 72 5) 1) 14) v2836_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2836 : Material (35 : Basis) (72 : Basis) where
  plus := ![v2836_pa,v2836_pb,v2836_pg]
  minus := ![(Primitive.Addresses.material2836 1).one,v2836_mb,v2836_mg]
  upper := v2836_upper
  lower := (Primitive.Addresses.material2836 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2836_pa_checked.trans (by decide +kernel)
    · exact v2836_pb_checked.trans (by decide +kernel)
    · exact v2836_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 72 Primitive.Addresses.material2836
    · exact v2836_mb_checked.trans (by decide +kernel)
    · exact v2836_mg_checked.trans (by decide +kernel)
  upper_error := v2836_upper_checked
  lower_error := reuse_lower_error 35 72 Primitive.Addresses.material2836

def v2837_pa : Scalar.QComplex := ((999999062899415459747019693385 : Int)/10^30,(-1369014350152327809750936124 : Int)/10^30)
theorem v2837_pa_checked : Scalar.distance (sourceCoefficient 35 73 1 0) v2837_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2837_pb : Scalar.QComplex := ((-590698879657319188390924 : Int)/10^30,(-431477088642151789259180090 : Int)/10^30)
theorem v2837_pb_checked : Scalar.distance (sourceCoefficient 35 73 1 1) v2837_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2837_pg : Scalar.QComplex := ((-93086339643056417167562 : Int)/10^30,(127436654195460889618 : Int)/10^30)
theorem v2837_pg_checked : Scalar.distance (sourceCoefficient 35 73 1 2) v2837_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2837_mb : Scalar.QComplex := ((-963043954204621688398216 : Int)/10^30,(-431476418236983156356253537 : Int)/10^30)
theorem v2837_mb_checked : Scalar.distance (sourceCoefficient 35 73 3 1) v2837_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2837_mg : Scalar.QComplex := ((-93086195010664875332170 : Int)/10^30,(207765925403821729402 : Int)/10^30)
theorem v2837_mg_checked : Scalar.distance (sourceCoefficient 35 73 3 2) v2837_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2837_upper : Scalar.QComplex := ((999995210723707061444764392362 : Int)/10^30,(-3094919974524333378396815308 : Int)/10^30)
theorem v2837_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 73 5) 1) 14) v2837_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2837 : Material (35 : Basis) (73 : Basis) where
  plus := ![v2837_pa,v2837_pb,v2837_pg]
  minus := ![(Primitive.Addresses.material2837 1).one,v2837_mb,v2837_mg]
  upper := v2837_upper
  lower := (Primitive.Addresses.material2837 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2837_pa_checked.trans (by decide +kernel)
    · exact v2837_pb_checked.trans (by decide +kernel)
    · exact v2837_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 73 Primitive.Addresses.material2837
    · exact v2837_mb_checked.trans (by decide +kernel)
    · exact v2837_mg_checked.trans (by decide +kernel)
  upper_error := v2837_upper_checked
  lower_error := reuse_lower_error 35 73 Primitive.Addresses.material2837

def v2838_pa : Scalar.QComplex := ((999999048285920022502986086824 : Int)/10^30,(-1379647510850254823309845322 : Int)/10^30)
theorem v2838_pa_checked : Scalar.distance (sourceCoefficient 35 74 1 0) v2838_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2838_pb : Scalar.QComplex := ((-595286847849441558316605 : Int)/10^30,(-431477081373996293441061793 : Int)/10^30)
theorem v2838_pb_checked : Scalar.distance (sourceCoefficient 35 74 1 1) v2838_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2838_pg : Scalar.QComplex := ((-93086338178885892091723 : Int)/10^30,(128426456987932320659 : Int)/10^30)
theorem v2838_pg_checked : Scalar.distance (sourceCoefficient 35 74 1 2) v2838_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2838_mb : Scalar.QComplex := ((-967631914416342972572788 : Int)/10^30,(-431476407009620451419735284 : Int)/10^30)
theorem v2838_mb_checked : Scalar.distance (sourceCoefficient 35 74 3 1) v2838_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2838_mg : Scalar.QComplex := ((-93086192692339664594008 : Int)/10^30,(208755726564231125236 : Int)/10^30)
theorem v2838_mg_checked : Scalar.distance (sourceCoefficient 35 74 3 2) v2838_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2838_upper : Scalar.QComplex := ((999995177758362657466755402911 : Int)/10^30,(-3105553094163849192457473234 : Int)/10^30)
theorem v2838_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 74 5) 1) 14) v2838_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2838 : Material (35 : Basis) (74 : Basis) where
  plus := ![v2838_pa,v2838_pb,v2838_pg]
  minus := ![(Primitive.Addresses.material2838 1).one,v2838_mb,v2838_mg]
  upper := v2838_upper
  lower := (Primitive.Addresses.material2838 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2838_pa_checked.trans (by decide +kernel)
    · exact v2838_pb_checked.trans (by decide +kernel)
    · exact v2838_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 74 Primitive.Addresses.material2838
    · exact v2838_mb_checked.trans (by decide +kernel)
    · exact v2838_mg_checked.trans (by decide +kernel)
  upper_error := v2838_upper_checked
  lower_error := reuse_lower_error 35 74 Primitive.Addresses.material2838

def v2839_pa : Scalar.QComplex := ((999999027736520338162558140641 : Int)/10^30,(-1394462625539817398936427813 : Int)/10^30)
theorem v2839_pa_checked : Scalar.distance (sourceCoefficient 35 75 1 0) v2839_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2839_pb : Scalar.QComplex := ((-601679234471287312832726 : Int)/10^30,(-431477071138871388012610504 : Int)/10^30)
theorem v2839_pb_checked : Scalar.distance (sourceCoefficient 35 75 1 1) v2839_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2839_pg : Scalar.QComplex := ((-93086336118394133147263 : Int)/10^30,(129805542870726608420 : Int)/10^30)
theorem v2839_pg_checked : Scalar.distance (sourceCoefficient 35 75 1 2) v2839_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2839_mb : Scalar.QComplex := ((-974024289825559220803654 : Int)/10^30,(-431476391258157604749176709 : Int)/10^30)
theorem v2839_mb_checked : Scalar.distance (sourceCoefficient 35 75 3 1) v2839_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2839_mg : Scalar.QComplex := ((-93086189441759667735795 : Int)/10^30,(210134810155417124628 : Int)/10^30)
theorem v2839_mg_checked : Scalar.distance (sourceCoefficient 35 75 3 2) v2839_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2839_upper : Scalar.QComplex := ((999995131639449641564004469297 : Int)/10^30,(-3120368151321639115407080310 : Int)/10^30)
theorem v2839_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 75 5) 1) 14) v2839_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2839 : Material (35 : Basis) (75 : Basis) where
  plus := ![v2839_pa,v2839_pb,v2839_pg]
  minus := ![(Primitive.Addresses.material2839 1).one,v2839_mb,v2839_mg]
  upper := v2839_upper
  lower := (Primitive.Addresses.material2839 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2839_pa_checked.trans (by decide +kernel)
    · exact v2839_pb_checked.trans (by decide +kernel)
    · exact v2839_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 75 Primitive.Addresses.material2839
    · exact v2839_mb_checked.trans (by decide +kernel)
    · exact v2839_mg_checked.trans (by decide +kernel)
  upper_error := v2839_upper_checked
  lower_error := reuse_lower_error 35 75 Primitive.Addresses.material2839

def v2840_pa : Scalar.QComplex := ((999999010325837297763176574471 : Int)/10^30,(-1406892798314614064283009896 : Int)/10^30)
theorem v2840_pa_checked : Scalar.distance (sourceCoefficient 35 76 1 0) v2840_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2840_pb : Scalar.QComplex := ((-607042572578803106821463 : Int)/10^30,(-431477062453982803755265422 : Int)/10^30)
theorem v2840_pb_checked : Scalar.distance (sourceCoefficient 35 76 1 1) v2840_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2840_pg : Scalar.QComplex := ((-93086334371211376632689 : Int)/10^30,(130962623058687735201 : Int)/10^30)
theorem v2840_pg_checked : Scalar.distance (sourceCoefficient 35 76 1 2) v2840_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2840_mb : Scalar.QComplex := ((-979387618441391425351209 : Int)/10^30,(-431476377944953023268030760 : Int)/10^30)
theorem v2840_mb_checked : Scalar.distance (sourceCoefficient 35 76 3 1) v2840_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2840_mg : Scalar.QComplex := ((-93086186696069472523901 : Int)/10^30,(211291888404804387573 : Int)/10^30)
theorem v2840_mg_checked : Scalar.distance (sourceCoefficient 35 76 3 2) v2840_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2840_upper : Scalar.QComplex := ((999995092775441979498125349389 : Int)/10^30,(-3132798275533894140455980893 : Int)/10^30)
theorem v2840_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 76 5) 1) 14) v2840_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2840 : Material (35 : Basis) (76 : Basis) where
  plus := ![v2840_pa,v2840_pb,v2840_pg]
  minus := ![(Primitive.Addresses.material2840 1).one,v2840_mb,v2840_mg]
  upper := v2840_upper
  lower := (Primitive.Addresses.material2840 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2840_pa_checked.trans (by decide +kernel)
    · exact v2840_pb_checked.trans (by decide +kernel)
    · exact v2840_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 76 Primitive.Addresses.material2840
    · exact v2840_mb_checked.trans (by decide +kernel)
    · exact v2840_mg_checked.trans (by decide +kernel)
  upper_error := v2840_upper_checked
  lower_error := reuse_lower_error 35 76 Primitive.Addresses.material2840

def v2841_pa : Scalar.QComplex := ((999999006273090576920798038073 : Int)/10^30,(-1409770488892779984050191643 : Int)/10^30)
theorem v2841_pa_checked : Scalar.distance (sourceCoefficient 35 77 1 0) v2841_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2841_pb : Scalar.QComplex := ((-608284230897796415654862 : Int)/10^30,(-431477060430685871800996517 : Int)/10^30)
theorem v2841_pb_checked : Scalar.distance (sourceCoefficient 35 77 1 1) v2841_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2841_pg : Scalar.QComplex := ((-93086333964331718443636 : Int)/10^30,(131230496949408672647 : Int)/10^30)
theorem v2841_pg_checked : Scalar.distance (sourceCoefficient 35 77 1 2) v2841_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2841_mb : Scalar.QComplex := ((-980629274552044469069410 : Int)/10^30,(-431476374850161637603210603 : Int)/10^30)
theorem v2841_mb_checked : Scalar.distance (sourceCoefficient 35 77 3 1) v2841_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2841_mg : Scalar.QComplex := ((-93086186058026862734750 : Int)/10^30,(211559761844664813224 : Int)/10^30)
theorem v2841_mg_checked : Scalar.distance (sourceCoefficient 35 77 3 2) v2841_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2841_upper : Scalar.QComplex := ((999995083756068418881487309527 : Int)/10^30,(-3135675954831404803462709492 : Int)/10^30)
theorem v2841_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 77 5) 1) 14) v2841_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2841 : Material (35 : Basis) (77 : Basis) where
  plus := ![v2841_pa,v2841_pb,v2841_pg]
  minus := ![(Primitive.Addresses.material2841 1).one,v2841_mb,v2841_mg]
  upper := v2841_upper
  lower := (Primitive.Addresses.material2841 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2841_pa_checked.trans (by decide +kernel)
    · exact v2841_pb_checked.trans (by decide +kernel)
    · exact v2841_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 77 Primitive.Addresses.material2841
    · exact v2841_mb_checked.trans (by decide +kernel)
    · exact v2841_mg_checked.trans (by decide +kernel)
  upper_error := v2841_upper_checked
  lower_error := reuse_lower_error 35 77 Primitive.Addresses.material2841

def v2842_pa : Scalar.QComplex := ((999998981735002433989227980131 : Int)/10^30,(-1427070060742785072297040835 : Int)/10^30)
theorem v2842_pa_checked : Scalar.distance (sourceCoefficient 35 78 1 0) v2842_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2842_pb : Scalar.QComplex := ((-615748604332040150167642 : Int)/10^30,(-431477048166993531005068113 : Int)/10^30)
theorem v2842_pb_checked : Scalar.distance (sourceCoefficient 35 78 1 1) v2842_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2842_pg : Scalar.QComplex := ((-93086331499373252578816 : Int)/10^30,(132840852014323468025 : Int)/10^30)
theorem v2842_pg_checked : Scalar.distance (sourceCoefficient 35 78 1 2) v2842_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2842_mb : Scalar.QComplex := ((-988093634623946681387169 : Int)/10^30,(-431476356145055772287858706 : Int)/10^30)
theorem v2842_mb_checked : Scalar.distance (sourceCoefficient 35 78 3 1) v2842_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2842_mg : Scalar.QComplex := ((-93086182203405421364921 : Int)/10^30,(213170114182822682639 : Int)/10^30)
theorem v2842_mg_checked : Scalar.distance (sourceCoefficient 35 78 3 2) v2842_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2842_upper : Scalar.QComplex := ((999995029360525214339691695510 : Int)/10^30,(-3152975458565215714854535375 : Int)/10^30)
theorem v2842_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 78 5) 1) 14) v2842_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2842 : Material (35 : Basis) (78 : Basis) where
  plus := ![v2842_pa,v2842_pb,v2842_pg]
  minus := ![(Primitive.Addresses.material2842 1).one,v2842_mb,v2842_mg]
  upper := v2842_upper
  lower := (Primitive.Addresses.material2842 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2842_pa_checked.trans (by decide +kernel)
    · exact v2842_pb_checked.trans (by decide +kernel)
    · exact v2842_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 78 Primitive.Addresses.material2842
    · exact v2842_mb_checked.trans (by decide +kernel)
    · exact v2842_mg_checked.trans (by decide +kernel)
  upper_error := v2842_upper_checked
  lower_error := reuse_lower_error 35 78 Primitive.Addresses.material2842

def v2843_pa : Scalar.QComplex := ((999998973760565112033347633616 : Int)/10^30,(-1432647136111525399910890404 : Int)/10^30)
theorem v2843_pa_checked : Scalar.distance (sourceCoefficient 35 79 1 0) v2843_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2843_pb : Scalar.QComplex := ((-618154986012633755047500 : Int)/10^30,(-431477044176696407648512564 : Int)/10^30)
theorem v2843_pb_checked : Scalar.distance (sourceCoefficient 35 79 1 1) v2843_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2843_pg : Scalar.QComplex := ((-93086330697786404090136 : Int)/10^30,(133360001944607095909 : Int)/10^30)
theorem v2843_pg_checked : Scalar.distance (sourceCoefficient 35 79 1 2) v2843_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2843_mb : Scalar.QComplex := ((-990500011965087708360592 : Int)/10^30,(-431476350078161123756667969 : Int)/10^30)
theorem v2843_mb_checked : Scalar.distance (sourceCoefficient 35 79 3 1) v2843_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2843_mg : Scalar.QComplex := ((-93086180953815863153782 : Int)/10^30,(213689263228069717040 : Int)/10^30)
theorem v2843_mg_checked : Scalar.distance (sourceCoefficient 35 79 3 2) v2843_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2843_upper : Scalar.QComplex := ((999995011760573631250854429569 : Int)/10^30,(-3158552511864402027629633930 : Int)/10^30)
theorem v2843_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 79 5) 1) 14) v2843_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2843 : Material (35 : Basis) (79 : Basis) where
  plus := ![v2843_pa,v2843_pb,v2843_pg]
  minus := ![(Primitive.Addresses.material2843 1).one,v2843_mb,v2843_mg]
  upper := v2843_upper
  lower := (Primitive.Addresses.material2843 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2843_pa_checked.trans (by decide +kernel)
    · exact v2843_pb_checked.trans (by decide +kernel)
    · exact v2843_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 79 Primitive.Addresses.material2843
    · exact v2843_mb_checked.trans (by decide +kernel)
    · exact v2843_mg_checked.trans (by decide +kernel)
  upper_error := v2843_upper_checked
  lower_error := reuse_lower_error 35 79 Primitive.Addresses.material2843

def v2844_pa : Scalar.QComplex := ((999998961241463189383291600291 : Int)/10^30,(-1441359078995215411157807663 : Int)/10^30)
theorem v2844_pa_checked : Scalar.distance (sourceCoefficient 35 80 1 0) v2844_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2844_pb : Scalar.QComplex := ((-621913991984621704047448 : Int)/10^30,(-431477037907649526293672523 : Int)/10^30)
theorem v2844_pb_checked : Scalar.distance (sourceCoefficient 35 80 1 1) v2844_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2844_pg : Scalar.QComplex := ((-93086329438868918393495 : Int)/10^30,(134170965438289052349 : Int)/10^30)
theorem v2844_pg_checked : Scalar.distance (sourceCoefficient 35 80 1 2) v2844_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2844_mb : Scalar.QComplex := ((-994259011127520827710740 : Int)/10^30,(-431476340565263722173182729 : Int)/10^30)
theorem v2844_mb_checked : Scalar.distance (sourceCoefficient 35 80 3 1) v2844_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2844_mg : Scalar.QComplex := ((-93086178995073875602031 : Int)/10^30,(214500225333403811303 : Int)/10^30)
theorem v2844_mg_checked : Scalar.distance (sourceCoefficient 35 80 3 2) v2844_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2844_upper : Scalar.QComplex := ((999994984205467278368156806812 : Int)/10^30,(-3167264420165842295880326558 : Int)/10^30)
theorem v2844_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 80 5) 1) 14) v2844_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2844 : Material (35 : Basis) (80 : Basis) where
  plus := ![v2844_pa,v2844_pb,v2844_pg]
  minus := ![(Primitive.Addresses.material2844 1).one,v2844_mb,v2844_mg]
  upper := v2844_upper
  lower := (Primitive.Addresses.material2844 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2844_pa_checked.trans (by decide +kernel)
    · exact v2844_pb_checked.trans (by decide +kernel)
    · exact v2844_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 80 Primitive.Addresses.material2844
    · exact v2844_mb_checked.trans (by decide +kernel)
    · exact v2844_mg_checked.trans (by decide +kernel)
  upper_error := v2844_upper_checked
  lower_error := reuse_lower_error 35 80 Primitive.Addresses.material2844

def v2845_pa : Scalar.QComplex := ((999998923087468646599841909420 : Int)/10^30,(-1467591190681587639446282043 : Int)/10^30)
theorem v2845_pa_checked : Scalar.distance (sourceCoefficient 35 81 1 0) v2845_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2845_pb : Scalar.QComplex := ((-633232553660876893996622 : Int)/10^30,(-431477018767546017352962779 : Int)/10^30)
theorem v2845_pb_checked : Scalar.distance (sourceCoefficient 35 81 1 1) v2845_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2845_pg : Scalar.QComplex := ((-93086325598428147555414 : Int)/10^30,(136612818541227346686 : Int)/10^30)
theorem v2845_pg_checked : Scalar.distance (sourceCoefficient 35 81 1 2) v2845_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2845_mb : Scalar.QComplex := ((-1005577552072310931813009 : Int)/10^30,(-431476311657758382453906623 : Int)/10^30)
theorem v2845_mb_checked : Scalar.distance (sourceCoefficient 35 81 3 1) v2845_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2845_mg : Scalar.QComplex := ((-93086173047425283881037 : Int)/10^30,(216942074213001179014 : Int)/10^30)
theorem v2845_mg_checked : Scalar.distance (sourceCoefficient 35 81 3 2) v2845_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2845_upper : Scalar.QComplex := ((999994900777284549381763343969 : Int)/10^30,(-3193496426932232330117892326 : Int)/10^30)
theorem v2845_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 81 5) 1) 14) v2845_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2845 : Material (35 : Basis) (81 : Basis) where
  plus := ![v2845_pa,v2845_pb,v2845_pg]
  minus := ![(Primitive.Addresses.material2845 1).one,v2845_mb,v2845_mg]
  upper := v2845_upper
  lower := (Primitive.Addresses.material2845 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2845_pa_checked.trans (by decide +kernel)
    · exact v2845_pb_checked.trans (by decide +kernel)
    · exact v2845_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 81 Primitive.Addresses.material2845
    · exact v2845_mb_checked.trans (by decide +kernel)
    · exact v2845_mg_checked.trans (by decide +kernel)
  upper_error := v2845_upper_checked
  lower_error := reuse_lower_error 35 81 Primitive.Addresses.material2845

def v2846_pa : Scalar.QComplex := ((999998908449827925695812197418 : Int)/10^30,(-1477531438808267869664369235 : Int)/10^30)
theorem v2846_pa_checked : Scalar.distance (sourceCoefficient 35 82 1 0) v2846_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2846_pb : Scalar.QComplex := ((-637521545369944321086021 : Int)/10^30,(-431477011411274462929183318 : Int)/10^30)
theorem v2846_pb_checked : Scalar.distance (sourceCoefficient 35 82 1 1) v2846_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2846_pg : Scalar.QComplex := ((-93086324123628797746428 : Int)/10^30,(137538120545517180442 : Int)/10^30)
theorem v2846_pg_checked : Scalar.distance (sourceCoefficient 35 82 1 2) v2846_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2846_mb : Scalar.QComplex := ((-1009866535836259691716213 : Int)/10^30,(-431476300600282891196840981 : Int)/10^30)
theorem v2846_mb_checked : Scalar.distance (sourceCoefficient 35 82 3 1) v2846_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2846_mg : Scalar.QComplex := ((-93086170774132527560384 : Int)/10^30,(217867374600073371795 : Int)/10^30)
theorem v2846_mg_checked : Scalar.distance (sourceCoefficient 35 82 3 2) v2846_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2846_upper : Scalar.QComplex := ((999994868983699135139846065352 : Int)/10^30,(-3203436634990840671327360002 : Int)/10^30)
theorem v2846_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 82 5) 1) 14) v2846_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2846 : Material (35 : Basis) (82 : Basis) where
  plus := ![v2846_pa,v2846_pb,v2846_pg]
  minus := ![(Primitive.Addresses.material2846 1).one,v2846_mb,v2846_mg]
  upper := v2846_upper
  lower := (Primitive.Addresses.material2846 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2846_pa_checked.trans (by decide +kernel)
    · exact v2846_pb_checked.trans (by decide +kernel)
    · exact v2846_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 82 Primitive.Addresses.material2846
    · exact v2846_mb_checked.trans (by decide +kernel)
    · exact v2846_mg_checked.trans (by decide +kernel)
  upper_error := v2846_upper_checked
  lower_error := reuse_lower_error 35 82 Primitive.Addresses.material2846

def v2847_pa : Scalar.QComplex := ((999998888309710450365591326130 : Int)/10^30,(-1491100044679755530184828534 : Int)/10^30)
theorem v2847_pa_checked : Scalar.distance (sourceCoefficient 35 83 1 0) v2847_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2847_pb : Scalar.QComplex := ((-643376091118991069029143 : Int)/10^30,(-431477001278084038390416044 : Int)/10^30)
theorem v2847_pb_checked : Scalar.distance (sourceCoefficient 35 83 1 1) v2847_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2847_pg : Scalar.QComplex := ((-93086322093181957688861 : Int)/10^30,(138801173336134307313 : Int)/10^30)
theorem v2847_pg_checked : Scalar.distance (sourceCoefficient 35 83 1 2) v2847_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2847_mb : Scalar.QComplex := ((-1015721070660904536908543 : Int)/10^30,(-431476285414886937232949224 : Int)/10^30)
theorem v2847_mb_checked : Scalar.distance (sourceCoefficient 35 83 3 1) v2847_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2847_mg : Scalar.QComplex := ((-93086167653728771014381 : Int)/10^30,(219130425168214045316 : Int)/10^30)
theorem v2847_mg_checked : Scalar.distance (sourceCoefficient 35 83 3 2) v2847_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2847_upper : Scalar.QComplex := ((999994825425428856270208473879 : Int)/10^30,(-3217005185893468101441506770 : Int)/10^30)
theorem v2847_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 83 5) 1) 14) v2847_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2847 : Material (35 : Basis) (83 : Basis) where
  plus := ![v2847_pa,v2847_pb,v2847_pg]
  minus := ![(Primitive.Addresses.material2847 1).one,v2847_mb,v2847_mg]
  upper := v2847_upper
  lower := (Primitive.Addresses.material2847 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2847_pa_checked.trans (by decide +kernel)
    · exact v2847_pb_checked.trans (by decide +kernel)
    · exact v2847_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 83 Primitive.Addresses.material2847
    · exact v2847_mb_checked.trans (by decide +kernel)
    · exact v2847_mg_checked.trans (by decide +kernel)
  upper_error := v2847_upper_checked
  lower_error := reuse_lower_error 35 83 Primitive.Addresses.material2847

def v2848_pa : Scalar.QComplex := ((999998835296484736780083944715 : Int)/10^30,(-1526239061874699027193854493 : Int)/10^30)
theorem v2848_pa_checked : Scalar.distance (sourceCoefficient 35 84 1 0) v2848_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2848_pb : Scalar.QComplex := ((-658537779849125632101607 : Int)/10^30,(-431476974543535167914809831 : Int)/10^30)
theorem v2848_pb_checked : Scalar.distance (sourceCoefficient 35 84 1 1) v2848_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2848_pg : Scalar.QComplex := ((-93086316741936641812169 : Int)/10^30,(142072138209503263791 : Int)/10^30)
theorem v2848_pg_checked : Scalar.distance (sourceCoefficient 35 84 1 2) v2848_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2848_mb : Scalar.QComplex := ((-1030882730674937866508981 : Int)/10^30,(-431476245596493504257146547 : Int)/10^30)
theorem v2848_mb_checked : Scalar.distance (sourceCoefficient 35 84 3 1) v2848_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2848_mg : Scalar.QComplex := ((-93086159479790080722640 : Int)/10^30,(222401384205769592499 : Int)/10^30)
theorem v2848_mg_checked : Scalar.distance (sourceCoefficient 35 84 3 2) v2848_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2848_upper : Scalar.QComplex := ((999994711765526207922856534699 : Int)/10^30,(-3252144059256954946118138070 : Int)/10^30)
theorem v2848_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 84 5) 1) 14) v2848_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2848 : Material (35 : Basis) (84 : Basis) where
  plus := ![v2848_pa,v2848_pb,v2848_pg]
  minus := ![(Primitive.Addresses.material2848 1).one,v2848_mb,v2848_mg]
  upper := v2848_upper
  lower := (Primitive.Addresses.material2848 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2848_pa_checked.trans (by decide +kernel)
    · exact v2848_pb_checked.trans (by decide +kernel)
    · exact v2848_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 84 Primitive.Addresses.material2848
    · exact v2848_mb_checked.trans (by decide +kernel)
    · exact v2848_mg_checked.trans (by decide +kernel)
  upper_error := v2848_upper_checked
  lower_error := reuse_lower_error 35 84 Primitive.Addresses.material2848

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
