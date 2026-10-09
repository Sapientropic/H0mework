import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B146

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3505_pa : Scalar.QComplex := ((999998802199936581514072496680 : Int)/10^30,(-1547772170609091914770226811 : Int)/10^30)
theorem v3505_pa_checked : Scalar.distance (sourceCoefficient 47 75 1 0) v3505_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3505_pb : Scalar.QComplex := ((-667828871826111165929652 : Int)/10^30,(-431476986459730049323566574 : Int)/10^30)
theorem v3505_pb_checked : Scalar.distance (sourceCoefficient 47 75 1 1) v3505_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3505_pg : Scalar.QComplex := ((-93086316486909517651230 : Int)/10^30,(144076582697888736126 : Int)/10^30)
theorem v3505_pg_checked : Scalar.distance (sourceCoefficient 47 75 1 2) v3505_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3505_mb : Scalar.QComplex := ((-1040173829475564730586120 : Int)/10^30,(-431476249494890027832290657 : Int)/10^30)
theorem v3505_mb_checked : Scalar.distance (sourceCoefficient 47 75 3 1) v3505_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3505_mg : Scalar.QComplex := ((-93086157495017734871816 : Int)/10^30,(224405827727731852014 : Int)/10^30)
theorem v3505_mg_checked : Scalar.distance (sourceCoefficient 47 75 3 2) v3505_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3505_upper : Scalar.QComplex := ((999994641504835138880131432610 : Int)/10^30,(-3273677078798672209858186748 : Int)/10^30)
theorem v3505_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 75 5) 1) 14) v3505_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3505 : Material (47 : Basis) (75 : Basis) where
  plus := ![v3505_pa,v3505_pb,v3505_pg]
  minus := ![(Primitive.Addresses.material3505 1).one,v3505_mb,v3505_mg]
  upper := v3505_upper
  lower := (Primitive.Addresses.material3505 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3505_pa_checked.trans (by decide +kernel)
    · exact v3505_pb_checked.trans (by decide +kernel)
    · exact v3505_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 75 Primitive.Addresses.material3505
    · exact v3505_mb_checked.trans (by decide +kernel)
    · exact v3505_mg_checked.trans (by decide +kernel)
  upper_error := v3505_upper_checked
  lower_error := reuse_lower_error 47 75 Primitive.Addresses.material3505

def v3506_pa : Scalar.QComplex := ((999998782883587555976583407638 : Int)/10^30,(-1560202340568583236534345018 : Int)/10^30)
theorem v3506_pa_checked : Scalar.distance (sourceCoefficient 47 76 1 0) v3506_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3506_pb : Scalar.QComplex := ((-673192209123799678477450 : Int)/10^30,(-431476977226673463552181986 : Int)/10^30)
theorem v3506_pb_checked : Scalar.distance (sourceCoefficient 47 76 1 1) v3506_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3506_pg : Scalar.QComplex := ((-93086314591900394944475 : Int)/10^30,(145233662667460931193 : Int)/10^30)
theorem v3506_pg_checked : Scalar.distance (sourceCoefficient 47 76 1 2) v3506_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3506_mb : Scalar.QComplex := ((-1045537156808525658492132 : Int)/10^30,(-431476235633518347789575298 : Int)/10^30)
theorem v3506_mb_checked : Scalar.distance (sourceCoefficient 47 76 3 1) v3506_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3506_mg : Scalar.QComplex := ((-93086154601501416970065 : Int)/10^30,(225562905631162768389 : Int)/10^30)
theorem v3506_mg_checked : Scalar.distance (sourceCoefficient 47 76 3 2) v3506_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3506_upper : Scalar.QComplex := ((999994600735169188903394919111 : Int)/10^30,(-3286107196906619474710552205 : Int)/10^30)
theorem v3506_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 76 5) 1) 14) v3506_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3506 : Material (47 : Basis) (76 : Basis) where
  plus := ![v3506_pa,v3506_pb,v3506_pg]
  minus := ![(Primitive.Addresses.material3506 1).one,v3506_mb,v3506_mg]
  upper := v3506_upper
  lower := (Primitive.Addresses.material3506 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3506_pa_checked.trans (by decide +kernel)
    · exact v3506_pb_checked.trans (by decide +kernel)
    · exact v3506_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 76 Primitive.Addresses.material3506
    · exact v3506_mb_checked.trans (by decide +kernel)
    · exact v3506_mg_checked.trans (by decide +kernel)
  upper_error := v3506_upper_checked
  lower_error := reuse_lower_error 47 76 Primitive.Addresses.material3506

def v3507_pa : Scalar.QComplex := ((999998778389662973273356361446 : Int)/10^30,(-1563080030491605300748028463 : Int)/10^30)
theorem v3507_pa_checked : Scalar.distance (sourceCoefficient 47 77 1 0) v3507_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3507_pb : Scalar.QComplex := ((-674433867254339763850274 : Int)/10^30,(-431476975076470983343916620 : Int)/10^30)
theorem v3507_pb_checked : Scalar.distance (sourceCoefficient 47 77 1 1) v3507_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3507_pg : Scalar.QComplex := ((-93086314150797677396086 : Int)/10^30,(145501536507361034236 : Int)/10^30)
theorem v3507_pg_checked : Scalar.distance (sourceCoefficient 47 77 1 2) v3507_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3507_mb : Scalar.QComplex := ((-1046778812621211776390027 : Int)/10^30,(-431476232411821623750138393 : Int)/10^30)
theorem v3507_mb_checked : Scalar.distance (sourceCoefficient 47 77 3 1) v3507_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3507_mg : Scalar.QComplex := ((-93086153929235804420479 : Int)/10^30,(225830778990669419682 : Int)/10^30)
theorem v3507_mg_checked : Scalar.distance (sourceCoefficient 47 77 3 2) v3507_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3507_upper : Scalar.QComplex := ((999994591274619554227369718107 : Int)/10^30,(-3288984874787554291694755035 : Int)/10^30)
theorem v3507_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 77 5) 1) 14) v3507_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3507 : Material (47 : Basis) (77 : Basis) where
  plus := ![v3507_pa,v3507_pb,v3507_pg]
  minus := ![(Primitive.Addresses.material3507 1).one,v3507_mb,v3507_mg]
  upper := v3507_upper
  lower := (Primitive.Addresses.material3507 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3507_pa_checked.trans (by decide +kernel)
    · exact v3507_pb_checked.trans (by decide +kernel)
    · exact v3507_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 77 Primitive.Addresses.material3507
    · exact v3507_mb_checked.trans (by decide +kernel)
    · exact v3507_mg_checked.trans (by decide +kernel)
  upper_error := v3507_upper_checked
  lower_error := reuse_lower_error 47 77 Primitive.Addresses.material3507

def v3508_pa : Scalar.QComplex := ((999998751199382766365475470120 : Int)/10^30,(-1580379598376379777148809958 : Int)/10^30)
theorem v3508_pa_checked : Scalar.distance (sourceCoefficient 47 78 1 0) v3508_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3508_pb : Scalar.QComplex := ((-681898239547978296409258 : Int)/10^30,(-431476962049871169966858451 : Int)/10^30)
theorem v3508_pb_checked : Scalar.distance (sourceCoefficient 47 78 1 1) v3508_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3508_pg : Scalar.QComplex := ((-93086311480103307218660 : Int)/10^30,(147111891264684868577 : Int)/10^30)
theorem v3508_pg_checked : Scalar.distance (sourceCoefficient 47 78 1 2) v3508_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3508_mb : Scalar.QComplex := ((-1054243170894154422692978 : Int)/10^30,(-431476212943809554209893702 : Int)/10^30)
theorem v3508_mb_checked : Scalar.distance (sourceCoefficient 47 78 3 1) v3508_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3508_mg : Scalar.QComplex := ((-93086149868878800780070 : Int)/10^30,(227441130843695623170 : Int)/10^30)
theorem v3508_mg_checked : Scalar.distance (sourceCoefficient 47 78 3 2) v3508_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3508_upper : Scalar.QComplex := ((999994534226895079466107333714 : Int)/10^30,(-3306284369978697599547149296 : Int)/10^30)
theorem v3508_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 78 5) 1) 14) v3508_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3508 : Material (47 : Basis) (78 : Basis) where
  plus := ![v3508_pa,v3508_pb,v3508_pg]
  minus := ![(Primitive.Addresses.material3508 1).one,v3508_mb,v3508_mg]
  upper := v3508_upper
  lower := (Primitive.Addresses.material3508 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3508_pa_checked.trans (by decide +kernel)
    · exact v3508_pb_checked.trans (by decide +kernel)
    · exact v3508_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 78 Primitive.Addresses.material3508
    · exact v3508_mb_checked.trans (by decide +kernel)
    · exact v3508_mg_checked.trans (by decide +kernel)
  upper_error := v3508_upper_checked
  lower_error := reuse_lower_error 47 78 Primitive.Addresses.material3508

def v3509_pa : Scalar.QComplex := ((999998742369925727826421269985 : Int)/10^30,(-1585956672457020007233315766 : Int)/10^30)
theorem v3509_pa_checked : Scalar.distance (sourceCoefficient 47 79 1 0) v3509_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3509_pb : Scalar.QComplex := ((-684304620858047759396144 : Int)/10^30,(-431476957813626198810156632 : Int)/10^30)
theorem v3509_pb_checked : Scalar.distance (sourceCoefficient 47 79 1 1) v3509_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3509_pg : Scalar.QComplex := ((-93086310612190849495130 : Int)/10^30,(147631041095047965887 : Int)/10^30)
theorem v3509_pg_checked : Scalar.distance (sourceCoefficient 47 79 1 2) v3509_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3509_mb : Scalar.QComplex := ((-1056649547652529530164839 : Int)/10^30,(-431476206630967469201827468 : Int)/10^30)
theorem v3509_mb_checked : Scalar.distance (sourceCoefficient 47 79 3 1) v3509_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3509_mg : Scalar.QComplex := ((-93086148552963744257053 : Int)/10^30,(227960279731786150627 : Int)/10^30)
theorem v3509_mg_checked : Scalar.distance (sourceCoefficient 47 79 3 2) v3509_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3509_upper : Scalar.QComplex := ((999994515771927276389439201143 : Int)/10^30,(-3311861420514099269226900392 : Int)/10^30)
theorem v3509_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 79 5) 1) 14) v3509_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3509 : Material (47 : Basis) (79 : Basis) where
  plus := ![v3509_pa,v3509_pb,v3509_pg]
  minus := ![(Primitive.Addresses.material3509 1).one,v3509_mb,v3509_mg]
  upper := v3509_upper
  lower := (Primitive.Addresses.material3509 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3509_pa_checked.trans (by decide +kernel)
    · exact v3509_pb_checked.trans (by decide +kernel)
    · exact v3509_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 79 Primitive.Addresses.material3509
    · exact v3509_mb_checked.trans (by decide +kernel)
    · exact v3509_mg_checked.trans (by decide +kernel)
  upper_error := v3509_upper_checked
  lower_error := reuse_lower_error 47 79 Primitive.Addresses.material3509

def v3510_pa : Scalar.QComplex := ((999998728515198510784045773251 : Int)/10^30,(-1594668613319027951320447022 : Int)/10^30)
theorem v3510_pa_checked : Scalar.distance (sourceCoefficient 47 80 1 0) v3510_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3510_pb : Scalar.QComplex := ((-688063626248495489668639 : Int)/10^30,(-431476951160384473798871596 : Int)/10^30)
theorem v3510_pb_checked : Scalar.distance (sourceCoefficient 47 80 1 1) v3510_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3510_pg : Scalar.QComplex := ((-93086309249666207617862 : Int)/10^30,(148442004431903954312 : Int)/10^30)
theorem v3510_pg_checked : Scalar.distance (sourceCoefficient 47 80 1 2) v3510_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3510_mb : Scalar.QComplex := ((-1060408545901879800739446 : Int)/10^30,(-431476196733875868858213261 : Int)/10^30)
theorem v3510_mb_checked : Scalar.distance (sourceCoefficient 47 80 3 1) v3510_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3510_mg : Scalar.QComplex := ((-93086146490614774436103 : Int)/10^30,(228771241590886025776 : Int)/10^30)
theorem v3510_mg_checked : Scalar.distance (sourceCoefficient 47 80 3 2) v3510_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3510_upper : Scalar.QComplex := ((999994486881201107611246897430 : Int)/10^30,(-3320573324488692390234821966 : Int)/10^30)
theorem v3510_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 80 5) 1) 14) v3510_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3510 : Material (47 : Basis) (80 : Basis) where
  plus := ![v3510_pa,v3510_pb,v3510_pg]
  minus := ![(Primitive.Addresses.material3510 1).one,v3510_mb,v3510_mg]
  upper := v3510_upper
  lower := (Primitive.Addresses.material3510 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3510_pa_checked.trans (by decide +kernel)
    · exact v3510_pb_checked.trans (by decide +kernel)
    · exact v3510_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 80 Primitive.Addresses.material3510
    · exact v3510_mb_checked.trans (by decide +kernel)
    · exact v3510_mg_checked.trans (by decide +kernel)
  upper_error := v3510_upper_checked
  lower_error := reuse_lower_error 47 80 Primitive.Addresses.material3510

def v3511_pa : Scalar.QComplex := ((999998686339566967566263259330 : Int)/10^30,(-1620900718847744282941747440 : Int)/10^30)
theorem v3511_pa_checked : Scalar.distance (sourceCoefficient 47 81 1 0) v3511_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3511_pb : Scalar.QComplex := ((-699382186153490694020168 : Int)/10^30,(-431476930863450376418834590 : Int)/10^30)
theorem v3511_pb_checked : Scalar.distance (sourceCoefficient 47 81 1 1) v3511_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3511_pg : Scalar.QComplex := ((-93086305097258918918420 : Int)/10^30,(150883857057180423813 : Int)/10^30)
theorem v3511_pg_checked : Scalar.distance (sourceCoefficient 47 81 1 2) v3511_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3511_mb : Scalar.QComplex := ((-1071727084077117882657570 : Int)/10^30,(-431476166669541899958100722 : Int)/10^30)
theorem v3511_mb_checked : Scalar.distance (sourceCoefficient 47 81 3 1) v3511_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3511_mg : Scalar.QComplex := ((-93086140231000193213782 : Int)/10^30,(231213089723608692043 : Int)/10^30)
theorem v3511_mg_checked : Scalar.distance (sourceCoefficient 47 81 3 2) v3511_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3511_upper : Scalar.QComplex := ((999994399431397995501877559367 : Int)/10^30,(-3346805318156455076219389597 : Int)/10^30)
theorem v3511_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 81 5) 1) 14) v3511_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3511 : Material (47 : Basis) (81 : Basis) where
  plus := ![v3511_pa,v3511_pb,v3511_pg]
  minus := ![(Primitive.Addresses.material3511 1).one,v3511_mb,v3511_mg]
  upper := v3511_upper
  lower := (Primitive.Addresses.material3511 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3511_pa_checked.trans (by decide +kernel)
    · exact v3511_pb_checked.trans (by decide +kernel)
    · exact v3511_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 81 Primitive.Addresses.material3511
    · exact v3511_mb_checked.trans (by decide +kernel)
    · exact v3511_mg_checked.trans (by decide +kernel)
  upper_error := v3511_upper_checked
  lower_error := reuse_lower_error 47 81 Primitive.Addresses.material3511

def v3512_pa : Scalar.QComplex := ((999998670177989855940765752216 : Int)/10^30,(-1630840964613514914300615676 : Int)/10^30)
theorem v3512_pa_checked : Scalar.distance (sourceCoefficient 47 82 1 0) v3512_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3512_pb : Scalar.QComplex := ((-703671177183438540122172 : Int)/10^30,(-431476923068815979364990033 : Int)/10^30)
theorem v3512_pb_checked : Scalar.distance (sourceCoefficient 47 82 1 1) v3512_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3512_pg : Scalar.QComplex := ((-93086303504244740535113 : Int)/10^30,(151809158878329724122 : Int)/10^30)
theorem v3512_pg_checked : Scalar.distance (sourceCoefficient 47 82 1 2) v3512_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3512_mb : Scalar.QComplex := ((-1076016066783659924380422 : Int)/10^30,(-431476155173704315343102446 : Int)/10^30)
theorem v3512_mb_checked : Scalar.distance (sourceCoefficient 47 82 3 1) v3512_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3512_mg : Scalar.QComplex := ((-93086137839492810377623 : Int)/10^30,(232138389825526346707 : Int)/10^30)
theorem v3512_mg_checked : Scalar.distance (sourceCoefficient 47 82 3 2) v3512_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3512_upper : Scalar.QComplex := ((999994366113882534978519907037 : Int)/10^30,(-3356745521223981374911313644 : Int)/10^30)
theorem v3512_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 82 5) 1) 14) v3512_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3512 : Material (47 : Basis) (82 : Basis) where
  plus := ![v3512_pa,v3512_pb,v3512_pg]
  minus := ![(Primitive.Addresses.material3512 1).one,v3512_mb,v3512_mg]
  upper := v3512_upper
  lower := (Primitive.Addresses.material3512 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3512_pa_checked.trans (by decide +kernel)
    · exact v3512_pb_checked.trans (by decide +kernel)
    · exact v3512_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 82 Primitive.Addresses.material3512
    · exact v3512_mb_checked.trans (by decide +kernel)
    · exact v3512_mg_checked.trans (by decide +kernel)
  upper_error := v3512_upper_checked
  lower_error := reuse_lower_error 47 82 Primitive.Addresses.material3512

def v3513_pa : Scalar.QComplex := ((999998647957673579054930437999 : Int)/10^30,(-1644409567237869637833979502 : Int)/10^30)
theorem v3513_pa_checked : Scalar.distance (sourceCoefficient 47 83 1 0) v3513_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3513_pb : Scalar.QComplex := ((-709525721998442088258948 : Int)/10^30,(-431476912337252903560368419 : Int)/10^30)
theorem v3513_pb_checked : Scalar.distance (sourceCoefficient 47 83 1 1) v3513_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3513_pg : Scalar.QComplex := ((-93086301312432671590273 : Int)/10^30,(153072211417060180708 : Int)/10^30)
theorem v3513_pg_checked : Scalar.distance (sourceCoefficient 47 83 1 2) v3513_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3513_mb : Scalar.QComplex := ((-1081870600157893269214739 : Int)/10^30,(-431476139389936738952055086 : Int)/10^30)
theorem v3513_mb_checked : Scalar.distance (sourceCoefficient 47 83 3 1) v3513_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3513_mg : Scalar.QComplex := ((-93086134557724102394848 : Int)/10^30,(233401440002529518822 : Int)/10^30)
theorem v3513_mg_checked : Scalar.distance (sourceCoefficient 47 83 3 2) v3513_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3513_upper : Scalar.QComplex := ((999994320475422157021897114125 : Int)/10^30,(-3370314065289246286937572021 : Int)/10^30)
theorem v3513_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 83 5) 1) 14) v3513_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3513 : Material (47 : Basis) (83 : Basis) where
  plus := ![v3513_pa,v3513_pb,v3513_pg]
  minus := ![(Primitive.Addresses.material3513 1).one,v3513_mb,v3513_mg]
  upper := v3513_upper
  lower := (Primitive.Addresses.material3513 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3513_pa_checked.trans (by decide +kernel)
    · exact v3513_pb_checked.trans (by decide +kernel)
    · exact v3513_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 83 Primitive.Addresses.material3513
    · exact v3513_mb_checked.trans (by decide +kernel)
    · exact v3513_mg_checked.trans (by decide +kernel)
  upper_error := v3513_upper_checked
  lower_error := reuse_lower_error 47 83 Primitive.Addresses.material3513

def v3514_pa : Scalar.QComplex := ((999998589557295934562153285773 : Int)/10^30,(-1679548575892419445566722482 : Int)/10^30)
theorem v3514_pa_checked : Scalar.distance (sourceCoefficient 47 84 1 0) v3514_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3514_pb : Scalar.QComplex := ((-724687408271918184429289 : Int)/10^30,(-431476884053080809270161630 : Int)/10^30)
theorem v3514_pb_checked : Scalar.distance (sourceCoefficient 47 84 1 1) v3514_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3514_pg : Scalar.QComplex := ((-93086295543295084065417 : Int)/10^30,(156343175627933524345 : Int)/10^30)
theorem v3514_pg_checked : Scalar.distance (sourceCoefficient 47 84 1 2) v3514_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3514_mb : Scalar.QComplex := ((-1097032256378013996926460 : Int)/10^30,(-431476098021922779142812485 : Int)/10^30)
theorem v3514_mb_checked : Scalar.distance (sourceCoefficient 47 84 3 1) v3514_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3514_mg : Scalar.QComplex := ((-93086125965893867759211 : Int)/10^30,(236672398016967490580 : Int)/10^30)
theorem v3514_mg_checked : Scalar.distance (sourceCoefficient 47 84 3 2) v3514_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3514_upper : Scalar.QComplex := ((999994201428390341241986399187 : Int)/10^30,(-3405452920814616648110659448 : Int)/10^30)
theorem v3514_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 84 5) 1) 14) v3514_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3514 : Material (47 : Basis) (84 : Basis) where
  plus := ![v3514_pa,v3514_pb,v3514_pg]
  minus := ![(Primitive.Addresses.material3514 1).one,v3514_mb,v3514_mg]
  upper := v3514_upper
  lower := (Primitive.Addresses.material3514 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3514_pa_checked.trans (by decide +kernel)
    · exact v3514_pb_checked.trans (by decide +kernel)
    · exact v3514_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 84 Primitive.Addresses.material3514
    · exact v3514_mb_checked.trans (by decide +kernel)
    · exact v3514_mg_checked.trans (by decide +kernel)
  upper_error := v3514_upper_checked
  lower_error := reuse_lower_error 47 84 Primitive.Addresses.material3514

def v3515_pa : Scalar.QComplex := ((999998453652545134251927959059 : Int)/10^30,(-1758605276502104941385664986 : Int)/10^30)
theorem v3515_pa_checked : Scalar.distance (sourceCoefficient 47 85 1 0) v3515_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3515_pb : Scalar.QComplex := ((-758798581875780750896251 : Int)/10^30,(-431476817821669192593796529 : Int)/10^30)
theorem v3515_pb_checked : Scalar.distance (sourceCoefficient 47 85 1 1) v3515_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3515_pg : Scalar.QComplex := ((-93086282073509393753047 : Int)/10^30,(163702279965040901555 : Int)/10^30)
theorem v3515_pg_checked : Scalar.distance (sourceCoefficient 47 85 1 2) v3515_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3515_mb : Scalar.QComplex := ((-1131143360126002399882748 : Int)/10^30,(-431476002354129313543123998 : Int)/10^30)
theorem v3515_mb_checked : Scalar.distance (sourceCoefficient 47 85 3 1) v3515_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3515_mg : Scalar.QComplex := ((-93086106145537591695634 : Int)/10^30,(244031487990125601289 : Int)/10^30)
theorem v3515_mg_checked : Scalar.distance (sourceCoefficient 47 85 3 2) v3515_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3515_upper : Scalar.QComplex := ((999993929079148670631391188247 : Int)/10^30,(-3484509269119362539555286300 : Int)/10^30)
theorem v3515_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 85 5) 1) 14) v3515_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3515 : Material (47 : Basis) (85 : Basis) where
  plus := ![v3515_pa,v3515_pb,v3515_pg]
  minus := ![(Primitive.Addresses.material3515 1).one,v3515_mb,v3515_mg]
  upper := v3515_upper
  lower := (Primitive.Addresses.material3515 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3515_pa_checked.trans (by decide +kernel)
    · exact v3515_pb_checked.trans (by decide +kernel)
    · exact v3515_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 85 Primitive.Addresses.material3515
    · exact v3515_mb_checked.trans (by decide +kernel)
    · exact v3515_mg_checked.trans (by decide +kernel)
  upper_error := v3515_upper_checked
  lower_error := reuse_lower_error 47 85 Primitive.Addresses.material3515

def v3516_pa : Scalar.QComplex := ((999998427897557306631900432395 : Int)/10^30,(-1773189897862224421679368840 : Int)/10^30)
theorem v3516_pa_checked : Scalar.distance (sourceCoefficient 47 86 1 0) v3516_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3516_pb : Scalar.QComplex := ((-765091514962908128359505 : Int)/10^30,(-431476805210242370539281424 : Int)/10^30)
theorem v3516_pb_checked : Scalar.distance (sourceCoefficient 47 86 1 1) v3516_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3516_pg : Scalar.QComplex := ((-93086279514402599368017 : Int)/10^30,(165059909955605650666 : Int)/10^30)
theorem v3516_pg_checked : Scalar.distance (sourceCoefficient 47 86 1 2) v3516_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3516_mb : Scalar.QComplex := ((-1137436279986889837904566 : Int)/10^30,(-431475984312189356293339708 : Int)/10^30)
theorem v3516_mb_checked : Scalar.distance (sourceCoefficient 47 86 3 1) v3516_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3516_mg : Scalar.QComplex := ((-93086102414858213710593 : Int)/10^30,(245389115266788752494 : Int)/10^30)
theorem v3516_mg_checked : Scalar.distance (sourceCoefficient 47 86 3 2) v3516_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3516_upper : Scalar.QComplex := ((999993878152465840988365669949 : Int)/10^30,(-3499093824306629217695844527 : Int)/10^30)
theorem v3516_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 86 5) 1) 14) v3516_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3516 : Material (47 : Basis) (86 : Basis) where
  plus := ![v3516_pa,v3516_pb,v3516_pg]
  minus := ![(Primitive.Addresses.material3516 1).one,v3516_mb,v3516_mg]
  upper := v3516_upper
  lower := (Primitive.Addresses.material3516 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3516_pa_checked.trans (by decide +kernel)
    · exact v3516_pb_checked.trans (by decide +kernel)
    · exact v3516_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 86 Primitive.Addresses.material3516
    · exact v3516_mb_checked.trans (by decide +kernel)
    · exact v3516_mg_checked.trans (by decide +kernel)
  upper_error := v3516_upper_checked
  lower_error := reuse_lower_error 47 86 Primitive.Addresses.material3516

def v3517_pa : Scalar.QComplex := ((999998426184621400673671910617 : Int)/10^30,(-1774155652783545015537327874 : Int)/10^30)
theorem v3517_pa_checked : Scalar.distance (sourceCoefficient 47 87 1 0) v3517_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3517_pb : Scalar.QComplex := ((-765508216288086170707067 : Int)/10^30,(-431476804370827229421135797 : Int)/10^30)
theorem v3517_pb_checked : Scalar.distance (sourceCoefficient 47 87 1 1) v3517_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3517_pg : Scalar.QComplex := ((-93086279344129859957207 : Int)/10^30,(165149808610284697862 : Int)/10^30)
theorem v3517_pg_checked : Scalar.distance (sourceCoefficient 47 87 1 2) v3517_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3517_mb : Scalar.QComplex := ((-1137852980432533471766557 : Int)/10^30,(-431475983113180051630166260 : Int)/10^30)
theorem v3517_mb_checked : Scalar.distance (sourceCoefficient 47 87 3 1) v3517_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3517_mg : Scalar.QComplex := ((-93086102167007047597194 : Int)/10^30,(245479013741056716669 : Int)/10^30)
theorem v3517_mg_checked : Scalar.distance (sourceCoefficient 47 87 3 2) v3517_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3517_upper : Scalar.QComplex := ((999993874772727104649678603216 : Int)/10^30,(-3500059574833199324436548594 : Int)/10^30)
theorem v3517_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 87 5) 1) 14) v3517_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3517 : Material (47 : Basis) (87 : Basis) where
  plus := ![v3517_pa,v3517_pb,v3517_pg]
  minus := ![(Primitive.Addresses.material3517 1).one,v3517_mb,v3517_mg]
  upper := v3517_upper
  lower := (Primitive.Addresses.material3517 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3517_pa_checked.trans (by decide +kernel)
    · exact v3517_pb_checked.trans (by decide +kernel)
    · exact v3517_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 87 Primitive.Addresses.material3517
    · exact v3517_mb_checked.trans (by decide +kernel)
    · exact v3517_mg_checked.trans (by decide +kernel)
  upper_error := v3517_upper_checked
  lower_error := reuse_lower_error 47 87 Primitive.Addresses.material3517

def v3518_pa : Scalar.QComplex := ((999998405252128108854584399803 : Int)/10^30,(-1785915227708615493640423678 : Int)/10^30)
theorem v3518_pa_checked : Scalar.distance (sourceCoefficient 47 88 1 0) v3518_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3518_pb : Scalar.QComplex := ((-770582205882188582580646 : Int)/10^30,(-431476794106590868618926819 : Int)/10^30)
theorem v3518_pb_checked : Scalar.distance (sourceCoefficient 47 88 1 1) v3518_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3518_pg : Scalar.QComplex := ((-93086277262667457639735 : Int)/10^30,(166244465172111116456 : Int)/10^30)
theorem v3518_pg_checked : Scalar.distance (sourceCoefficient 47 88 1 2) v3518_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3518_mb : Scalar.QComplex := ((-1142926959279783969648216 : Int)/10^30,(-431475968470323016969980173 : Int)/10^30)
theorem v3518_mb_checked : Scalar.distance (sourceCoefficient 47 88 3 1) v3518_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3518_mg : Scalar.QComplex := ((-93086099140906108948489 : Int)/10^30,(246573668099084161406 : Int)/10^30)
theorem v3518_mg_checked : Scalar.distance (sourceCoefficient 47 88 3 2) v3518_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3518_upper : Scalar.QComplex := ((999993833544305488952460173402 : Int)/10^30,(-3511819096116179887631950819 : Int)/10^30)
theorem v3518_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 88 5) 1) 14) v3518_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3518 : Material (47 : Basis) (88 : Basis) where
  plus := ![v3518_pa,v3518_pb,v3518_pg]
  minus := ![(Primitive.Addresses.material3518 1).one,v3518_mb,v3518_mg]
  upper := v3518_upper
  lower := (Primitive.Addresses.material3518 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3518_pa_checked.trans (by decide +kernel)
    · exact v3518_pb_checked.trans (by decide +kernel)
    · exact v3518_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 88 Primitive.Addresses.material3518
    · exact v3518_mb_checked.trans (by decide +kernel)
    · exact v3518_mg_checked.trans (by decide +kernel)
  upper_error := v3518_upper_checked
  lower_error := reuse_lower_error 47 88 Primitive.Addresses.material3518

def v3519_pa : Scalar.QComplex := ((999998376388237136884407513630 : Int)/10^30,(-1802004686345480811191265341 : Int)/10^30)
theorem v3519_pa_checked : Scalar.distance (sourceCoefficient 47 89 1 0) v3519_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3519_pb : Scalar.QComplex := ((-777524441888453289447539 : Int)/10^30,(-431476779934165264337146603 : Int)/10^30)
theorem v3519_pb_checked : Scalar.distance (sourceCoefficient 47 89 1 1) v3519_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3519_pg : Scalar.QComplex := ((-93086274390478336470648 : Int)/10^30,(167742175034251791544 : Int)/10^30)
theorem v3519_pg_checked : Scalar.distance (sourceCoefficient 47 89 1 2) v3519_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3519_mb : Scalar.QComplex := ((-1149869180470971941382670 : Int)/10^30,(-431475948307065683026510821 : Int)/10^30)
theorem v3519_mb_checked : Scalar.distance (sourceCoefficient 47 89 3 1) v3519_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3519_mg : Scalar.QComplex := ((-93086094976261900547443 : Int)/10^30,(248071374924989153124 : Int)/10^30)
theorem v3519_mg_checked : Scalar.distance (sourceCoefficient 47 89 3 2) v3519_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3519_upper : Scalar.QComplex := ((999993776911511523413334358330 : Int)/10^30,(-3527908480973229260262448173 : Int)/10^30)
theorem v3519_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 89 5) 1) 14) v3519_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3519 : Material (47 : Basis) (89 : Basis) where
  plus := ![v3519_pa,v3519_pb,v3519_pg]
  minus := ![(Primitive.Addresses.material3519 1).one,v3519_mb,v3519_mg]
  upper := v3519_upper
  lower := (Primitive.Addresses.material3519 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3519_pa_checked.trans (by decide +kernel)
    · exact v3519_pb_checked.trans (by decide +kernel)
    · exact v3519_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 89 Primitive.Addresses.material3519
    · exact v3519_mb_checked.trans (by decide +kernel)
    · exact v3519_mg_checked.trans (by decide +kernel)
  upper_error := v3519_upper_checked
  lower_error := reuse_lower_error 47 89 Primitive.Addresses.material3519

def v3520_pa : Scalar.QComplex := ((999998328827116917249484324210 : Int)/10^30,(-1828207584861931339492826718 : Int)/10^30)
theorem v3520_pa_checked : Scalar.distance (sourceCoefficient 47 90 1 0) v3520_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3520_pb : Scalar.QComplex := ((-788830397260018519038453 : Int)/10^30,(-431476756534528153440838169 : Int)/10^30)
theorem v3520_pb_checked : Scalar.distance (sourceCoefficient 47 90 1 1) v3520_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3520_pg : Scalar.QComplex := ((-93086269652726421038891 : Int)/10^30,(170181308628005648970 : Int)/10^30)
theorem v3520_pg_checked : Scalar.distance (sourceCoefficient 47 90 1 2) v3520_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3520_mb : Scalar.QComplex := ((-1161175111439980332283567 : Int)/10^30,(-431475915150907000551215387 : Int)/10^30)
theorem v3520_mb_checked : Scalar.distance (sourceCoefficient 47 90 3 1) v3520_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3520_mg : Scalar.QComplex := ((-93086088133649312286742 : Int)/10^30,(250510503522075577091 : Int)/10^30)
theorem v3520_mg_checked : Scalar.distance (sourceCoefficient 47 90 3 2) v3520_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3520_upper : Scalar.QComplex := ((999993684126636409470905552509 : Int)/10^30,(-3554111258377361669020780920 : Int)/10^30)
theorem v3520_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 47 90 5) 1) 14) v3520_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3520 : Material (47 : Basis) (90 : Basis) where
  plus := ![v3520_pa,v3520_pb,v3520_pg]
  minus := ![(Primitive.Addresses.material3520 1).one,v3520_mb,v3520_mg]
  upper := v3520_upper
  lower := (Primitive.Addresses.material3520 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3520_pa_checked.trans (by decide +kernel)
    · exact v3520_pb_checked.trans (by decide +kernel)
    · exact v3520_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 47 90 Primitive.Addresses.material3520
    · exact v3520_mb_checked.trans (by decide +kernel)
    · exact v3520_mg_checked.trans (by decide +kernel)
  upper_error := v3520_upper_checked
  lower_error := reuse_lower_error 47 90 Primitive.Addresses.material3520

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
