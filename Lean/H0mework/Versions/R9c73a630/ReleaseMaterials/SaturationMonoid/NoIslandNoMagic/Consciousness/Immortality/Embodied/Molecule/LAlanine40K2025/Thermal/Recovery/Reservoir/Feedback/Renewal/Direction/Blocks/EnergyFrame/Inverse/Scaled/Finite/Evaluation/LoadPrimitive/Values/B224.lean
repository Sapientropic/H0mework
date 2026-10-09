import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B149
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B150

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3585_pa : Scalar.QComplex := ((999999242126714370453063356479 : Int)/10^30,(-1231156365733929348130996179 : Int)/10^30)
theorem v3585_pa_checked : Scalar.distance (sourceCoefficient 49 58 1 0) v3585_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3585_pb : Scalar.QComplex := ((-531216296072998818427813 : Int)/10^30,(-431477193525848650628703004 : Int)/10^30)
theorem v3585_pb_checked : Scalar.distance (sourceCoefficient 49 58 1 1) v3585_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3585_pg : Scalar.QComplex := ((-93086359298611012324066 : Int)/10^30,(114603950668753333936 : Int)/10^30)
theorem v3585_pg_checked : Scalar.distance (sourceCoefficient 49 58 1 2) v3585_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3585_mb : Scalar.QComplex := ((-903561483278292280253886 : Int)/10^30,(-431476574451431601884865160 : Int)/10^30)
theorem v3585_mb_checked : Scalar.distance (sourceCoefficient 49 58 3 1) v3585_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3585_mg : Scalar.QComplex := ((-93086225740257331864187 : Int)/10^30,(194933243617174542541 : Int)/10^30)
theorem v3585_mg_checked : Scalar.distance (sourceCoefficient 49 58 3 2) v3585_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3585_upper : Scalar.QComplex := ((999995627881113761646374379277 : Int)/10^30,(-2957062504759267317902318334 : Int)/10^30)
theorem v3585_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 58 5) 1) 14) v3585_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3585 : Material (49 : Basis) (58 : Basis) where
  plus := ![v3585_pa,v3585_pb,v3585_pg]
  minus := ![(Primitive.Addresses.material3585 1).one,v3585_mb,v3585_mg]
  upper := v3585_upper
  lower := (Primitive.Addresses.material3585 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3585_pa_checked.trans (by decide +kernel)
    · exact v3585_pb_checked.trans (by decide +kernel)
    · exact v3585_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 58 Primitive.Addresses.material3585
    · exact v3585_mb_checked.trans (by decide +kernel)
    · exact v3585_mg_checked.trans (by decide +kernel)
  upper_error := v3585_upper_checked
  lower_error := reuse_lower_error 49 58 Primitive.Addresses.material3585

def v3586_pa : Scalar.QComplex := ((999999220346030718523745074714 : Int)/10^30,(-1248722279252933283504537166 : Int)/10^30)
theorem v3586_pa_checked : Scalar.distance (sourceCoefficient 49 59 1 0) v3586_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3586_pb : Scalar.QComplex := ((-538795592601418730599537 : Int)/10^30,(-431477183901642701977201811 : Int)/10^30)
theorem v3586_pb_checked : Scalar.distance (sourceCoefficient 49 59 1 1) v3586_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3586_pg : Scalar.QComplex := ((-93086357246710792207826 : Int)/10^30,(116239098814740280302 : Int)/10^30)
theorem v3586_pg_checked : Scalar.distance (sourceCoefficient 49 59 1 2) v3586_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3586_mb : Scalar.QComplex := ((-911140768679337428390426 : Int)/10^30,(-431476558286637691582506491 : Int)/10^30)
theorem v3586_mb_checked : Scalar.distance (sourceCoefficient 49 59 3 1) v3586_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3586_mg : Scalar.QComplex := ((-93086222277298670116129 : Int)/10^30,(196568389383623628388 : Int)/10^30)
theorem v3586_mg_checked : Scalar.distance (sourceCoefficient 49 59 3 2) v3586_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3586_upper : Scalar.QComplex := ((999995575783289382912204368996 : Int)/10^30,(-2974628354524422448825789637 : Int)/10^30)
theorem v3586_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 59 5) 1) 14) v3586_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3586 : Material (49 : Basis) (59 : Basis) where
  plus := ![v3586_pa,v3586_pb,v3586_pg]
  minus := ![(Primitive.Addresses.material3586 1).one,v3586_mb,v3586_mg]
  upper := v3586_upper
  lower := (Primitive.Addresses.material3586 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3586_pa_checked.trans (by decide +kernel)
    · exact v3586_pb_checked.trans (by decide +kernel)
    · exact v3586_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 59 Primitive.Addresses.material3586
    · exact v3586_mb_checked.trans (by decide +kernel)
    · exact v3586_mg_checked.trans (by decide +kernel)
  upper_error := v3586_upper_checked
  lower_error := reuse_lower_error 49 59 Primitive.Addresses.material3586

def v3587_pa : Scalar.QComplex := ((999999194836696340713043698761 : Int)/10^30,(-1268986193396377482063048019 : Int)/10^30)
theorem v3587_pa_checked : Scalar.distance (sourceCoefficient 49 60 1 0) v3587_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3587_pb : Scalar.QComplex := ((-547539015626421799347511 : Int)/10^30,(-431477172578717930928153153 : Int)/10^30)
theorem v3587_pb_checked : Scalar.distance (sourceCoefficient 49 60 1 1) v3587_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3587_pg : Scalar.QComplex := ((-93086354838027424852526 : Int)/10^30,(118125394193285523160 : Int)/10^30)
theorem v3587_pg_checked : Scalar.distance (sourceCoefficient 49 60 1 2) v3587_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3587_mb : Scalar.QComplex := ((-919884178677590398942708 : Int)/10^30,(-431476539418536855153090569 : Int)/10^30)
theorem v3587_mb_checked : Scalar.distance (sourceCoefficient 49 60 3 1) v3587_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3587_mg : Scalar.QComplex := ((-93086218240828243529334 : Int)/10^30,(198454681981229630901 : Int)/10^30)
theorem v3587_mg_checked : Scalar.distance (sourceCoefficient 49 60 3 2) v3587_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3587_upper : Scalar.QComplex := ((999995515300315514604698646930 : Int)/10^30,(-2994892194460349949927121105 : Int)/10^30)
theorem v3587_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 60 5) 1) 14) v3587_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3587 : Material (49 : Basis) (60 : Basis) where
  plus := ![v3587_pa,v3587_pb,v3587_pg]
  minus := ![(Primitive.Addresses.material3587 1).one,v3587_mb,v3587_mg]
  upper := v3587_upper
  lower := (Primitive.Addresses.material3587 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3587_pa_checked.trans (by decide +kernel)
    · exact v3587_pb_checked.trans (by decide +kernel)
    · exact v3587_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 60 Primitive.Addresses.material3587
    · exact v3587_mb_checked.trans (by decide +kernel)
    · exact v3587_mg_checked.trans (by decide +kernel)
  upper_error := v3587_upper_checked
  lower_error := reuse_lower_error 49 60 Primitive.Addresses.material3587

def v3588_pa : Scalar.QComplex := ((999999187384114486427296435925 : Int)/10^30,(-1274845524243062171217683642 : Int)/10^30)
theorem v3588_pa_checked : Scalar.distance (sourceCoefficient 49 61 1 0) v3588_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3588_pb : Scalar.QComplex := ((-550067185038343074462219 : Int)/10^30,(-431477169260653602906211091 : Int)/10^30)
theorem v3588_pb_checked : Scalar.distance (sourceCoefficient 49 61 1 1) v3588_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3588_pg : Scalar.QComplex := ((-93086354133242746432186 : Int)/10^30,(118670818368661339511 : Int)/10^30)
theorem v3588_pg_checked : Scalar.distance (sourceCoefficient 49 61 1 2) v3588_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3588_mb : Scalar.QComplex := ((-922412344284818583935981 : Int)/10^30,(-431476533918777424633543574 : Int)/10^30)
theorem v3588_mb_checked : Scalar.distance (sourceCoefficient 49 61 3 1) v3588_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3588_mg : Scalar.QComplex := ((-93086217065367329176175 : Int)/10^30,(199000105345321664490 : Int)/10^30)
theorem v3588_mg_checked : Scalar.distance (sourceCoefficient 49 61 3 2) v3588_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3588_upper : Scalar.QComplex := ((999995497735071273028544685161 : Int)/10^30,(-3000751503717769440742845428 : Int)/10^30)
theorem v3588_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 61 5) 1) 14) v3588_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3588 : Material (49 : Basis) (61 : Basis) where
  plus := ![v3588_pa,v3588_pb,v3588_pg]
  minus := ![(Primitive.Addresses.material3588 1).one,v3588_mb,v3588_mg]
  upper := v3588_upper
  lower := (Primitive.Addresses.material3588 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3588_pa_checked.trans (by decide +kernel)
    · exact v3588_pb_checked.trans (by decide +kernel)
    · exact v3588_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 61 Primitive.Addresses.material3588
    · exact v3588_mb_checked.trans (by decide +kernel)
    · exact v3588_mg_checked.trans (by decide +kernel)
  upper_error := v3588_upper_checked
  lower_error := reuse_lower_error 49 61 Primitive.Addresses.material3588

def v3589_pa : Scalar.QComplex := ((999999176494652812668480487734 : Int)/10^30,(-1283358880521581224662995167 : Int)/10^30)
theorem v3589_pa_checked : Scalar.distance (sourceCoefficient 49 62 1 0) v3589_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3589_pb : Scalar.QComplex := ((-553740506688991278312935 : Int)/10^30,(-431477164404451448438265475 : Int)/10^30)
theorem v3589_pb_checked : Scalar.distance (sourceCoefficient 49 62 1 1) v3589_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3589_pg : Scalar.QComplex := ((-93086353102576650073040 : Int)/10^30,(119463296288222674778 : Int)/10^30)
theorem v3589_pg_checked : Scalar.distance (sourceCoefficient 49 62 1 2) v3589_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3589_mb : Scalar.QComplex := ((-926085660377037514077649 : Int)/10^30,(-431476525892665934107913398 : Int)/10^30)
theorem v3589_mb_checked : Scalar.distance (sourceCoefficient 49 62 3 1) v3589_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3589_mg : Scalar.QComplex := ((-93086215350828863880240 : Int)/10^30,(199792582080388830595 : Int)/10^30)
theorem v3589_mg_checked : Scalar.distance (sourceCoefficient 49 62 3 2) v3589_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3589_upper : Scalar.QComplex := ((999995472152345206768349897326 : Int)/10^30,(-3009264828522421401750516747 : Int)/10^30)
theorem v3589_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 62 5) 1) 14) v3589_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3589 : Material (49 : Basis) (62 : Basis) where
  plus := ![v3589_pa,v3589_pb,v3589_pg]
  minus := ![(Primitive.Addresses.material3589 1).one,v3589_mb,v3589_mg]
  upper := v3589_upper
  lower := (Primitive.Addresses.material3589 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3589_pa_checked.trans (by decide +kernel)
    · exact v3589_pb_checked.trans (by decide +kernel)
    · exact v3589_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 62 Primitive.Addresses.material3589
    · exact v3589_mb_checked.trans (by decide +kernel)
    · exact v3589_mg_checked.trans (by decide +kernel)
  upper_error := v3589_upper_checked
  lower_error := reuse_lower_error 49 62 Primitive.Addresses.material3589

def v3590_pa : Scalar.QComplex := ((999999144366146221384562579002 : Int)/10^30,(-1308154033532725511810250793 : Int)/10^30)
theorem v3590_pa_checked : Scalar.distance (sourceCoefficient 49 63 1 0) v3590_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3590_pb : Scalar.QComplex := ((-564439057133209272187705 : Int)/10^30,(-431477150023192038388360617 : Int)/10^30)
theorem v3590_pb_checked : Scalar.distance (sourceCoefficient 49 63 1 1) v3590_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3590_pg : Scalar.QComplex := ((-93086350055915050320671 : Int)/10^30,(121771388484206930773 : Int)/10^30)
theorem v3590_pg_checked : Scalar.distance (sourceCoefficient 49 63 1 2) v3590_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3590_mb : Scalar.QComplex := ((-936784194427317066666957 : Int)/10^30,(-431476502279044690323101101 : Int)/10^30)
theorem v3590_mb_checked : Scalar.distance (sourceCoefficient 49 63 3 1) v3590_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3590_mg : Scalar.QComplex := ((-93086210312388786018416 : Int)/10^30,(202100670787833132959 : Int)/10^30)
theorem v3590_mg_checked : Scalar.distance (sourceCoefficient 49 63 3 2) v3590_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3590_upper : Scalar.QComplex := ((999995397229701768595713166291 : Int)/10^30,(-3034059889153210220866801041 : Int)/10^30)
theorem v3590_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 63 5) 1) 14) v3590_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3590 : Material (49 : Basis) (63 : Basis) where
  plus := ![v3590_pa,v3590_pb,v3590_pg]
  minus := ![(Primitive.Addresses.material3590 1).one,v3590_mb,v3590_mg]
  upper := v3590_upper
  lower := (Primitive.Addresses.material3590 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3590_pa_checked.trans (by decide +kernel)
    · exact v3590_pb_checked.trans (by decide +kernel)
    · exact v3590_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 63 Primitive.Addresses.material3590
    · exact v3590_mb_checked.trans (by decide +kernel)
    · exact v3590_mg_checked.trans (by decide +kernel)
  upper_error := v3590_upper_checked
  lower_error := reuse_lower_error 49 63 Primitive.Addresses.material3590

def v3591_pa : Scalar.QComplex := ((999999097380837071586454002865 : Int)/10^30,(-1343591273838690054777138351 : Int)/10^30)
theorem v3591_pa_checked : Scalar.distance (sourceCoefficient 49 64 1 0) v3591_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3591_pb : Scalar.QComplex := ((-579729428466122112557317 : Int)/10^30,(-431477128855506557509226447 : Int)/10^30)
theorem v3591_pb_checked : Scalar.distance (sourceCoefficient 49 64 1 1) v3591_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3591_pg : Scalar.QComplex := ((-93086345585722487511582 : Int)/10^30,(125070114533191487209 : Int)/10^30)
theorem v3591_pg_checked : Scalar.distance (sourceCoefficient 49 64 1 2) v3591_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3591_mb : Scalar.QComplex := ((-952074541800166642466647 : Int)/10^30,(-431476467916465283597743506 : Int)/10^30)
theorem v3591_mb_checked : Scalar.distance (sourceCoefficient 49 64 3 1) v3591_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3591_mg : Scalar.QComplex := ((-93086202995545876498745 : Int)/10^30,(205399391750976370424 : Int)/10^30)
theorem v3591_mg_checked : Scalar.distance (sourceCoefficient 49 64 3 2) v3591_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3591_upper : Scalar.QComplex := ((999995289083000671129094743568 : Int)/10^30,(-3069496995587186960161040746 : Int)/10^30)
theorem v3591_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 64 5) 1) 14) v3591_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3591 : Material (49 : Basis) (64 : Basis) where
  plus := ![v3591_pa,v3591_pb,v3591_pg]
  minus := ![(Primitive.Addresses.material3591 1).one,v3591_mb,v3591_mg]
  upper := v3591_upper
  lower := (Primitive.Addresses.material3591 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3591_pa_checked.trans (by decide +kernel)
    · exact v3591_pb_checked.trans (by decide +kernel)
    · exact v3591_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 64 Primitive.Addresses.material3591
    · exact v3591_mb_checked.trans (by decide +kernel)
    · exact v3591_mg_checked.trans (by decide +kernel)
  upper_error := v3591_upper_checked
  lower_error := reuse_lower_error 49 64 Primitive.Addresses.material3591

def v3592_pa : Scalar.QComplex := ((999999048409603559229852324061 : Int)/10^30,(-1379557859372798360431363841 : Int)/10^30)
theorem v3592_pa_checked : Scalar.distance (sourceCoefficient 49 65 1 0) v3592_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3592_pb : Scalar.QComplex := ((-595248200027313316852874 : Int)/10^30,(-431477106632893107450693175 : Int)/10^30)
theorem v3592_pb_checked : Scalar.distance (sourceCoefficient 49 65 1 1) v3592_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3592_pg : Scalar.QComplex := ((-93086340909304188806608 : Int)/10^30,(128418115403131581802 : Int)/10^30)
theorem v3592_pg_checked : Scalar.distance (sourceCoefficient 49 65 1 2) v3592_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3592_mb : Scalar.QComplex := ((-967593288405895413588321 : Int)/10^30,(-431476432301859190251073270 : Int)/10^30)
theorem v3592_mb_checked : Scalar.distance (sourceCoefficient 49 65 3 1) v3592_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3592_mg : Scalar.QComplex := ((-93086195429955356641380 : Int)/10^30,(208747387338764356219 : Int)/10^30)
theorem v3592_mg_checked : Scalar.distance (sourceCoefficient 49 65 3 2) v3592_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3592_upper : Scalar.QComplex := ((999995178036776326952875087432 : Int)/10^30,(-3105463443033384637955843426 : Int)/10^30)
theorem v3592_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 65 5) 1) 14) v3592_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3592 : Material (49 : Basis) (65 : Basis) where
  plus := ![v3592_pa,v3592_pb,v3592_pg]
  minus := ![(Primitive.Addresses.material3592 1).one,v3592_mb,v3592_mg]
  upper := v3592_upper
  lower := (Primitive.Addresses.material3592 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3592_pa_checked.trans (by decide +kernel)
    · exact v3592_pb_checked.trans (by decide +kernel)
    · exact v3592_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 65 Primitive.Addresses.material3592
    · exact v3592_mb_checked.trans (by decide +kernel)
    · exact v3592_mg_checked.trans (by decide +kernel)
  upper_error := v3592_upper_checked
  lower_error := reuse_lower_error 49 65 Primitive.Addresses.material3592

def v3593_pa : Scalar.QComplex := ((999999023991876839830882296541 : Int)/10^30,(-1397145408942276759744102299 : Int)/10^30)
theorem v3593_pa_checked : Scalar.distance (sourceCoefficient 49 66 1 0) v3593_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3593_pb : Scalar.QComplex := ((-602836831408466488506287 : Int)/10^30,(-431477095495167854610760997 : Int)/10^30)
theorem v3593_pb_checked : Scalar.distance (sourceCoefficient 49 66 1 1) v3593_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3593_pg : Scalar.QComplex := ((-93086338571405109695541 : Int)/10^30,(130055277505292327620 : Int)/10^30)
theorem v3593_pg_checked : Scalar.distance (sourceCoefficient 49 66 1 2) v3593_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3593_mb : Scalar.QComplex := ((-975181907350099035774502 : Int)/10^30,(-431476414615490981830049037 : Int)/10^30)
theorem v3593_mb_checked : Scalar.distance (sourceCoefficient 49 66 3 1) v3593_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3593_mg : Scalar.QComplex := ((-93086191679259988916172 : Int)/10^30,(210384546813833219191 : Int)/10^30)
theorem v3593_mg_checked : Scalar.distance (sourceCoefficient 49 66 3 2) v3593_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3593_upper : Scalar.QComplex := ((999995123264570948003175164823 : Int)/10^30,(-3123050924265492773411515404 : Int)/10^30)
theorem v3593_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 66 5) 1) 14) v3593_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3593 : Material (49 : Basis) (66 : Basis) where
  plus := ![v3593_pa,v3593_pb,v3593_pg]
  minus := ![(Primitive.Addresses.material3593 1).one,v3593_mb,v3593_mg]
  upper := v3593_upper
  lower := (Primitive.Addresses.material3593 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3593_pa_checked.trans (by decide +kernel)
    · exact v3593_pb_checked.trans (by decide +kernel)
    · exact v3593_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 66 Primitive.Addresses.material3593
    · exact v3593_mb_checked.trans (by decide +kernel)
    · exact v3593_mg_checked.trans (by decide +kernel)
  upper_error := v3593_upper_checked
  lower_error := reuse_lower_error 49 66 Primitive.Addresses.material3593

def v3594_pa : Scalar.QComplex := ((999998982316488461423843769047 : Int)/10^30,(-1426662534518034736134129397 : Int)/10^30)
theorem v3594_pa_checked : Scalar.distance (sourceCoefficient 49 67 1 0) v3594_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3594_pb : Scalar.QComplex := ((-615572805865560101375034 : Int)/10^30,(-431477076402810552138145139 : Int)/10^30)
theorem v3594_pb_checked : Scalar.distance (sourceCoefficient 49 67 1 1) v3594_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3594_pg : Scalar.QComplex := ((-93086334572217705591313 : Int)/10^30,(132802921161137022473 : Int)/10^30)
theorem v3594_pg_checked : Scalar.distance (sourceCoefficient 49 67 1 2) v3594_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3594_mb : Scalar.QComplex := ((-987917860589162831298622 : Int)/10^30,(-431476384532568438839087713 : Int)/10^30)
theorem v3594_mb_checked : Scalar.distance (sourceCoefficient 49 67 3 1) v3594_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3594_mg : Scalar.QComplex := ((-93086185308981348174684 : Int)/10^30,(213132185995485994427 : Int)/10^30)
theorem v3594_mg_checked : Scalar.distance (sourceCoefficient 49 67 3 2) v3594_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3594_upper : Scalar.QComplex := ((999995030645363669147944255848 : Int)/10^30,(-3152567933951019950415922516 : Int)/10^30)
theorem v3594_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 67 5) 1) 14) v3594_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3594 : Material (49 : Basis) (67 : Basis) where
  plus := ![v3594_pa,v3594_pb,v3594_pg]
  minus := ![(Primitive.Addresses.material3594 1).one,v3594_mb,v3594_mg]
  upper := v3594_upper
  lower := (Primitive.Addresses.material3594 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3594_pa_checked.trans (by decide +kernel)
    · exact v3594_pb_checked.trans (by decide +kernel)
    · exact v3594_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 67 Primitive.Addresses.material3594
    · exact v3594_mb_checked.trans (by decide +kernel)
    · exact v3594_mg_checked.trans (by decide +kernel)
  upper_error := v3594_upper_checked
  lower_error := reuse_lower_error 49 67 Primitive.Addresses.material3594

def v3595_pa : Scalar.QComplex := ((999998910976383356987406598687 : Int)/10^30,(-1475820465813368364191169468 : Int)/10^30)
theorem v3595_pa_checked : Scalar.distance (sourceCoefficient 49 68 1 0) v3595_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3595_pb : Scalar.QComplex := ((-636783344788941587824852 : Int)/10^30,(-431477043493830837130041874 : Int)/10^30)
theorem v3595_pb_checked : Scalar.distance (sourceCoefficient 49 68 1 1) v3595_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3595_pg : Scalar.QComplex := ((-93086327701948448961223 : Int)/10^30,(137378857118765245205 : Int)/10^30)
theorem v3595_pg_checked : Scalar.distance (sourceCoefficient 49 68 1 2) v3595_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3595_mb : Scalar.QComplex := ((-1009128363215923978430691 : Int)/10^30,(-431476333319861173681105134 : Int)/10^30)
theorem v3595_mb_checked : Scalar.distance (sourceCoefficient 49 68 3 1) v3595_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3595_mg : Scalar.QComplex := ((-93086174489888010731688 : Int)/10^30,(217708114320551186499 : Int)/10^30)
theorem v3595_mg_checked : Scalar.distance (sourceCoefficient 49 68 3 2) v3595_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3595_upper : Scalar.QComplex := ((999994874463234974362863259115 : Int)/10^30,(-3201725668904839923841600556 : Int)/10^30)
theorem v3595_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 68 5) 1) 14) v3595_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3595 : Material (49 : Basis) (68 : Basis) where
  plus := ![v3595_pa,v3595_pb,v3595_pg]
  minus := ![(Primitive.Addresses.material3595 1).one,v3595_mb,v3595_mg]
  upper := v3595_upper
  lower := (Primitive.Addresses.material3595 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3595_pa_checked.trans (by decide +kernel)
    · exact v3595_pb_checked.trans (by decide +kernel)
    · exact v3595_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 68 Primitive.Addresses.material3595
    · exact v3595_mb_checked.trans (by decide +kernel)
    · exact v3595_mg_checked.trans (by decide +kernel)
  upper_error := v3595_upper_checked
  lower_error := reuse_lower_error 49 68 Primitive.Addresses.material3595

def v3596_pa : Scalar.QComplex := ((999998878812390558092341688857 : Int)/10^30,(-1497455829673169274867961987 : Int)/10^30)
theorem v3596_pa_checked : Scalar.distance (sourceCoefficient 49 69 1 0) v3596_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3596_pb : Scalar.QComplex := ((-646118516221330974758618 : Int)/10^30,(-431477028569367756601709336 : Int)/10^30)
theorem v3596_pb_checked : Scalar.distance (sourceCoefficient 49 69 1 1) v3596_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3596_pg : Scalar.QComplex := ((-93086324595040161152811 : Int)/10^30,(139392815713189630283 : Int)/10^30)
theorem v3596_pg_checked : Scalar.distance (sourceCoefficient 49 69 1 2) v3596_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3596_mb : Scalar.QComplex := ((-1018463518293262937044030 : Int)/10^30,(-431476310339571144574247519 : Int)/10^30)
theorem v3596_mb_checked : Scalar.distance (sourceCoefficient 49 69 3 1) v3596_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3596_mg : Scalar.QComplex := ((-93086169645025318106932 : Int)/10^30,(219722069483964821994 : Int)/10^30)
theorem v3596_mg_checked : Scalar.distance (sourceCoefficient 49 69 3 2) v3596_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3596_upper : Scalar.QComplex := ((999994804958614802817692033523 : Int)/10^30,(-3223360945029174157452816153 : Int)/10^30)
theorem v3596_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 69 5) 1) 14) v3596_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3596 : Material (49 : Basis) (69 : Basis) where
  plus := ![v3596_pa,v3596_pb,v3596_pg]
  minus := ![(Primitive.Addresses.material3596 1).one,v3596_mb,v3596_mg]
  upper := v3596_upper
  lower := (Primitive.Addresses.material3596 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3596_pa_checked.trans (by decide +kernel)
    · exact v3596_pb_checked.trans (by decide +kernel)
    · exact v3596_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 69 Primitive.Addresses.material3596
    · exact v3596_mb_checked.trans (by decide +kernel)
    · exact v3596_mg_checked.trans (by decide +kernel)
  upper_error := v3596_upper_checked
  lower_error := reuse_lower_error 49 69 Primitive.Addresses.material3596

def v3597_pa : Scalar.QComplex := ((999998857399375541167542672156 : Int)/10^30,(-1511687779728829421664133231 : Int)/10^30)
theorem v3597_pa_checked : Scalar.distance (sourceCoefficient 49 70 1 0) v3597_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3597_pb : Scalar.QComplex := ((-652259281530986169772624 : Int)/10^30,(-431477018605077072245828619 : Int)/10^30)
theorem v3597_pb_checked : Scalar.distance (sourceCoefficient 49 70 1 1) v3597_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3597_pg : Scalar.QComplex := ((-93086322523567690145140 : Int)/10^30,(140717617002810827052 : Int)/10^30)
theorem v3597_pg_checked : Scalar.distance (sourceCoefficient 49 70 1 2) v3597_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3597_mb : Scalar.QComplex := ((-1024604272717696474828508 : Int)/10^30,(-431476295076080277949539069 : Int)/10^30)
theorem v3597_mb_checked : Scalar.distance (sourceCoefficient 49 70 3 1) v3597_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3597_mg : Scalar.QComplex := ((-93086166430309772295188 : Int)/10^30,(221046868492714505404 : Int)/10^30)
theorem v3597_mg_checked : Scalar.distance (sourceCoefficient 49 70 3 2) v3597_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3597_upper : Scalar.QComplex := ((999994758982576994417430637653 : Int)/10^30,(-3237592836931095152970022832 : Int)/10^30)
theorem v3597_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 70 5) 1) 14) v3597_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3597 : Material (49 : Basis) (70 : Basis) where
  plus := ![v3597_pa,v3597_pb,v3597_pg]
  minus := ![(Primitive.Addresses.material3597 1).one,v3597_mb,v3597_mg]
  upper := v3597_upper
  lower := (Primitive.Addresses.material3597 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3597_pa_checked.trans (by decide +kernel)
    · exact v3597_pb_checked.trans (by decide +kernel)
    · exact v3597_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 70 Primitive.Addresses.material3597
    · exact v3597_mb_checked.trans (by decide +kernel)
    · exact v3597_mg_checked.trans (by decide +kernel)
  upper_error := v3597_upper_checked
  lower_error := reuse_lower_error 49 70 Primitive.Addresses.material3597

def v3598_pa : Scalar.QComplex := ((999998820381151565606442643486 : Int)/10^30,(-1535980568030780633231071037 : Int)/10^30)
theorem v3598_pa_checked : Scalar.distance (sourceCoefficient 49 71 1 0) v3598_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3598_pb : Scalar.QComplex := ((-662741071373293634403253 : Int)/10^30,(-431477001327632079481410788 : Int)/10^30)
theorem v3598_pb_checked : Scalar.distance (sourceCoefficient 49 71 1 1) v3598_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3598_pg : Scalar.QComplex := ((-93086318936913164875729 : Int)/10^30,(142978945697273568776 : Int)/10^30)
theorem v3598_pg_checked : Scalar.distance (sourceCoefficient 49 71 1 2) v3598_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3598_mb : Scalar.QComplex := ((-1035086043747497658187745 : Int)/10^30,(-431476268753329166746147489 : Int)/10^30)
theorem v3598_mb_checked : Scalar.distance (sourceCoefficient 49 71 3 1) v3598_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3598_mg : Scalar.QComplex := ((-93086160892231765643509 : Int)/10^30,(223308193250059907969 : Int)/10^30)
theorem v3598_mg_checked : Scalar.distance (sourceCoefficient 49 71 3 2) v3598_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3598_upper : Scalar.QComplex := ((999994680037259368524105453174 : Int)/10^30,(-3261885525161695505378510517 : Int)/10^30)
theorem v3598_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 71 5) 1) 14) v3598_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3598 : Material (49 : Basis) (71 : Basis) where
  plus := ![v3598_pa,v3598_pb,v3598_pg]
  minus := ![(Primitive.Addresses.material3598 1).one,v3598_mb,v3598_mg]
  upper := v3598_upper
  lower := (Primitive.Addresses.material3598 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3598_pa_checked.trans (by decide +kernel)
    · exact v3598_pb_checked.trans (by decide +kernel)
    · exact v3598_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 71 Primitive.Addresses.material3598
    · exact v3598_mb_checked.trans (by decide +kernel)
    · exact v3598_mg_checked.trans (by decide +kernel)
  upper_error := v3598_upper_checked
  lower_error := reuse_lower_error 49 71 Primitive.Addresses.material3598

def v3599_pa : Scalar.QComplex := ((999998779541176427877631946737 : Int)/10^30,(-1562343162568487928881284671 : Int)/10^30)
theorem v3599_pa_checked : Scalar.distance (sourceCoefficient 49 72 1 0) v3599_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3599_pb : Scalar.QComplex := ((-674115935667179781750623 : Int)/10^30,(-431476982193972395801008154 : Int)/10^30)
theorem v3599_pb_checked : Scalar.distance (sourceCoefficient 49 72 1 1) v3599_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3599_pg : Scalar.QComplex := ((-93086314972153316143806 : Int)/10^30,(145432945220361632570 : Int)/10^30)
theorem v3599_pg_checked : Scalar.distance (sourceCoefficient 49 72 1 2) v3599_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3599_mb : Scalar.QComplex := ((-1046460887294515412967989 : Int)/10^30,(-431476239803681026648097294 : Int)/10^30)
theorem v3599_mb_checked : Scalar.distance (sourceCoefficient 49 72 3 1) v3599_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3599_mg : Scalar.QComplex := ((-93086154809782328783551 : Int)/10^30,(225762188438002612698 : Int)/10^30)
theorem v3599_mg_checked : Scalar.distance (sourceCoefficient 49 72 3 2) v3599_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3599_upper : Scalar.QComplex := ((999994593697898480952408556617 : Int)/10^30,(-3288248009949322890887087926 : Int)/10^30)
theorem v3599_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 72 5) 1) 14) v3599_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3599 : Material (49 : Basis) (72 : Basis) where
  plus := ![v3599_pa,v3599_pb,v3599_pg]
  minus := ![(Primitive.Addresses.material3599 1).one,v3599_mb,v3599_mg]
  upper := v3599_upper
  lower := (Primitive.Addresses.material3599 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3599_pa_checked.trans (by decide +kernel)
    · exact v3599_pb_checked.trans (by decide +kernel)
    · exact v3599_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 72 Primitive.Addresses.material3599
    · exact v3599_mb_checked.trans (by decide +kernel)
    · exact v3599_mg_checked.trans (by decide +kernel)
  upper_error := v3599_upper_checked
  lower_error := reuse_lower_error 49 72 Primitive.Addresses.material3599

def v3600_pa : Scalar.QComplex := ((999998764732944057616945067963 : Int)/10^30,(-1571792793595920076834976602 : Int)/10^30)
theorem v3600_pa_checked : Scalar.distance (sourceCoefficient 49 73 1 0) v3600_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3600_pb : Scalar.QComplex := ((-678193238031727295295210 : Int)/10^30,(-431476975238196679767542387 : Int)/10^30)
theorem v3600_pb_checked : Scalar.distance (sourceCoefficient 49 73 1 1) v3600_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3600_pg : Scalar.QComplex := ((-93086313532615323572873 : Int)/10^30,(146312577528082029601 : Int)/10^30)
theorem v3600_pg_checked : Scalar.distance (sourceCoefficient 49 73 1 2) v3600_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3600_mb : Scalar.QComplex := ((-1050538182138375747839998 : Int)/10^30,(-431476229329379594844973057 : Int)/10^30)
theorem v3600_mb_checked : Scalar.distance (sourceCoefficient 49 73 3 1) v3600_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3600_mg : Scalar.QComplex := ((-93086152611161807824182 : Int)/10^30,(226641819175939247178 : Int)/10^30)
theorem v3600_mg_checked : Scalar.distance (sourceCoefficient 49 73 3 2) v3600_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3600_upper : Scalar.QComplex := ((999994562580482276296683745942 : Int)/10^30,(-3297697601344973976393226566 : Int)/10^30)
theorem v3600_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 73 5) 1) 14) v3600_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3600 : Material (49 : Basis) (73 : Basis) where
  plus := ![v3600_pa,v3600_pb,v3600_pg]
  minus := ![(Primitive.Addresses.material3600 1).one,v3600_mb,v3600_mg]
  upper := v3600_upper
  lower := (Primitive.Addresses.material3600 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3600_pa_checked.trans (by decide +kernel)
    · exact v3600_pb_checked.trans (by decide +kernel)
    · exact v3600_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 73 Primitive.Addresses.material3600
    · exact v3600_mb_checked.trans (by decide +kernel)
    · exact v3600_mg_checked.trans (by decide +kernel)
  upper_error := v3600_upper_checked
  lower_error := reuse_lower_error 49 73 Primitive.Addresses.material3600

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
