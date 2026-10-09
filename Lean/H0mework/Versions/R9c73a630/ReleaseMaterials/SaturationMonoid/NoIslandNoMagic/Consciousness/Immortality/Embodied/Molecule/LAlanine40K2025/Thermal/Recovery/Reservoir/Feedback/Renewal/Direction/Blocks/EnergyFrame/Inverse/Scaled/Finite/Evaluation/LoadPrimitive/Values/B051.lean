import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B034

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v817_pa : Scalar.QComplex := ((999999559766819265081539676958 : Int)/10^30,(-938331587267839716020858705 : Int)/10^30)
theorem v817_pa_checked : Scalar.distance (sourceCoefficient 8 78 1 0) v817_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v817_pb : Scalar.QComplex := ((-404868894620201494920537 : Int)/10^30,(-431477232437996885031918424 : Int)/10^30)
theorem v817_pb_checked : Scalar.distance (sourceCoefficient 8 78 1 1) v817_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v817_pg : Scalar.QComplex := ((-93086378280032055748527 : Int)/10^30,(87345927537092542301 : Int)/10^30)
theorem v817_pg_checked : Scalar.distance (sourceCoefficient 8 78 1 2) v817_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v817_mb : Scalar.QComplex := ((-777214162449838267319462 : Int)/10^30,(-431476722395682325559964285 : Int)/10^30)
theorem v817_mb_checked : Scalar.distance (sourceCoefficient 8 78 3 1) v817_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v817_mg : Scalar.QComplex := ((-93086268244117614472237 : Int)/10^30,(167675247015032985028 : Int)/10^30)
theorem v817_mg_checked : Scalar.distance (sourceCoefficient 8 78 3 2) v817_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v817_upper : Scalar.QComplex := ((999996450909748344732769429186 : Int)/10^30,(-2664238710639292559165025466 : Int)/10^30)
theorem v817_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 78 5) 1) 14) v817_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material817 : Material (8 : Basis) (78 : Basis) where
  plus := ![v817_pa,v817_pb,v817_pg]
  minus := ![(Primitive.Addresses.material817 1).one,v817_mb,v817_mg]
  upper := v817_upper
  lower := (Primitive.Addresses.material817 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v817_pa_checked.trans (by decide +kernel)
    · exact v817_pb_checked.trans (by decide +kernel)
    · exact v817_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 78 Primitive.Addresses.material817
    · exact v817_mb_checked.trans (by decide +kernel)
    · exact v817_mg_checked.trans (by decide +kernel)
  upper_error := v817_upper_checked
  lower_error := reuse_lower_error 8 78 Primitive.Addresses.material817

def v818_pa : Scalar.QComplex := ((999999554518116022675540086873 : Int)/10^30,(-943908665867911167065413092 : Int)/10^30)
theorem v818_pa_checked : Scalar.distance (sourceCoefficient 8 79 1 0) v818_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v818_pb : Scalar.QComplex := ((-407275277230292843235267 : Int)/10^30,(-431477229231761676552262068 : Int)/10^30)
theorem v818_pb_checked : Scalar.distance (sourceCoefficient 8 79 1 1) v818_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v818_pg : Scalar.QComplex := ((-93086377689885907845164 : Int)/10^30,(87865077718037055620 : Int)/10^30)
theorem v818_pg_checked : Scalar.distance (sourceCoefficient 8 79 1 2) v818_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v818_mb : Scalar.QComplex := ((-779620541397086811334260 : Int)/10^30,(-431476717112848497848898872 : Int)/10^30)
theorem v818_mb_checked : Scalar.distance (sourceCoefficient 8 79 3 1) v818_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v818_mg : Scalar.QComplex := ((-93086267205968461808324 : Int)/10^30,(168194396493404613202 : Int)/10^30)
theorem v818_mg_checked : Scalar.distance (sourceCoefficient 8 79 3 2) v818_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v818_upper : Scalar.QComplex := ((999996436035521204548713675242 : Int)/10^30,(-2669815771874174927321716023 : Int)/10^30)
theorem v818_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 79 5) 1) 14) v818_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material818 : Material (8 : Basis) (79 : Basis) where
  plus := ![v818_pa,v818_pb,v818_pg]
  minus := ![(Primitive.Addresses.material818 1).one,v818_mb,v818_mg]
  upper := v818_upper
  lower := (Primitive.Addresses.material818 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v818_pa_checked.trans (by decide +kernel)
    · exact v818_pb_checked.trans (by decide +kernel)
    · exact v818_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 79 Primitive.Addresses.material818
    · exact v818_mb_checked.trans (by decide +kernel)
    · exact v818_mg_checked.trans (by decide +kernel)
  upper_error := v818_upper_checked
  lower_error := reuse_lower_error 8 79 Primitive.Addresses.material818

def v819_pa : Scalar.QComplex := ((999999546256880111972253506431 : Int)/10^30,(-952620613829680176980197811 : Int)/10^30)
theorem v819_pa_checked : Scalar.distance (sourceCoefficient 8 80 1 0) v819_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v819_pb : Scalar.QComplex := ((-411034284662998615223790 : Int)/10^30,(-431477224187496992115031945 : Int)/10^30)
theorem v819_pb_checked : Scalar.distance (sourceCoefficient 8 80 1 1) v819_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v819_pg : Scalar.QComplex := ((-93086376761259692525405 : Int)/10^30,(88676041605635861953 : Int)/10^30)
theorem v819_pg_checked : Scalar.distance (sourceCoefficient 8 80 1 2) v819_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v819_mb : Scalar.QComplex := ((-783379543077169083578443 : Int)/10^30,(-431476708824731576606943375 : Int)/10^30)
theorem v819_mb_checked : Scalar.distance (sourceCoefficient 8 80 3 1) v819_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v819_mg : Scalar.QComplex := ((-93086265577517281718420 : Int)/10^30,(169005359277681901252 : Int)/10^30)
theorem v819_mg_checked : Scalar.distance (sourceCoefficient 8 80 3 2) v819_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v819_upper : Scalar.QComplex := ((999996412738265757717852814415 : Int)/10^30,(-2678527692602377097071021161 : Int)/10^30)
theorem v819_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 80 5) 1) 14) v819_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material819 : Material (8 : Basis) (80 : Basis) where
  plus := ![v819_pa,v819_pb,v819_pg]
  minus := ![(Primitive.Addresses.material819 1).one,v819_mb,v819_mg]
  upper := v819_upper
  lower := (Primitive.Addresses.material819 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v819_pa_checked.trans (by decide +kernel)
    · exact v819_pb_checked.trans (by decide +kernel)
    · exact v819_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 80 Primitive.Addresses.material819
    · exact v819_mb_checked.trans (by decide +kernel)
    · exact v819_mg_checked.trans (by decide +kernel)
  upper_error := v819_upper_checked
  lower_error := reuse_lower_error 8 80 Primitive.Addresses.material819

def v820_pa : Scalar.QComplex := ((999999520923540931494833094691 : Int)/10^30,(-978852741030415003553934025 : Int)/10^30)
theorem v820_pa_checked : Scalar.distance (sourceCoefficient 8 81 1 0) v820_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v820_pb : Scalar.QComplex := ((-422352850801985852210703 : Int)/10^30,(-431477208735276179473387395 : Int)/10^30)
theorem v820_pb_checked : Scalar.distance (sourceCoefficient 8 81 1 1) v820_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v820_pg : Scalar.QComplex := ((-93086373915343062746041 : Int)/10^30,(91117895912054612638 : Int)/10^30)
theorem v820_pg_checked : Scalar.distance (sourceCoefficient 8 81 1 2) v820_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v820_mb : Scalar.QComplex := ((-794698091667166243874580 : Int)/10^30,(-431476683605103708882697463 : Int)/10^30)
theorem v820_mb_checked : Scalar.distance (sourceCoefficient 8 81 3 1) v820_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v820_mg : Scalar.QComplex := ((-93086260624391422199922 : Int)/10^30,(171447210218988819229 : Int)/10^30)
theorem v820_mg_checked : Scalar.distance (sourceCoefficient 8 81 3 2) v820_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v820_upper : Scalar.QComplex := ((999996342130692519794953787006 : Int)/10^30,(-2704759737010394697344430170 : Int)/10^30)
theorem v820_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 81 5) 1) 14) v820_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material820 : Material (8 : Basis) (81 : Basis) where
  plus := ![v820_pa,v820_pb,v820_pg]
  minus := ![(Primitive.Addresses.material820 1).one,v820_mb,v820_mg]
  upper := v820_upper
  lower := (Primitive.Addresses.material820 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v820_pa_checked.trans (by decide +kernel)
    · exact v820_pb_checked.trans (by decide +kernel)
    · exact v820_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 81 Primitive.Addresses.material820
    · exact v820_mb_checked.trans (by decide +kernel)
    · exact v820_mg_checked.trans (by decide +kernel)
  upper_error := v820_upper_checked
  lower_error := reuse_lower_error 8 81 Primitive.Addresses.material820

def v821_pa : Scalar.QComplex := ((999999511144086906915108513270 : Int)/10^30,(-988792995123886391349457773 : Int)/10^30)
theorem v821_pa_checked : Scalar.distance (sourceCoefficient 8 82 1 0) v821_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v821_pb : Scalar.QComplex := ((-426641844227410613100399 : Int)/10^30,(-431477202776470049719920525 : Int)/10^30)
theorem v821_pb_checked : Scalar.distance (sourceCoefficient 8 82 1 1) v821_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v821_pg : Scalar.QComplex := ((-93086372817403070328816 : Int)/10^30,(92043198379200492517 : Int)/10^30)
theorem v821_pg_checked : Scalar.distance (sourceCoefficient 8 82 1 2) v821_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v821_mb : Scalar.QComplex := ((-798987078353421420483981 : Int)/10^30,(-431476673945091640816622276 : Int)/10^30)
theorem v821_mb_checked : Scalar.distance (sourceCoefficient 8 82 3 1) v821_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v821_mg : Scalar.QComplex := ((-93086258727957483525147 : Int)/10^30,(172372511394129538104 : Int)/10^30)
theorem v821_mg_checked : Scalar.distance (sourceCoefficient 8 82 3 2) v821_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v821_upper : Scalar.QComplex := ((999996315195276268038705248271 : Int)/10^30,(-2714699959420574815898277454 : Int)/10^30)
theorem v821_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 82 5) 1) 14) v821_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material821 : Material (8 : Basis) (82 : Basis) where
  plus := ![v821_pa,v821_pb,v821_pg]
  minus := ![(Primitive.Addresses.material821 1).one,v821_mb,v821_mg]
  upper := v821_upper
  lower := (Primitive.Addresses.material821 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v821_pa_checked.trans (by decide +kernel)
    · exact v821_pb_checked.trans (by decide +kernel)
    · exact v821_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 82 Primitive.Addresses.material821
    · exact v821_mb_checked.trans (by decide +kernel)
    · exact v821_mg_checked.trans (by decide +kernel)
  upper_error := v821_upper_checked
  lower_error := reuse_lower_error 8 82 Primitive.Addresses.material821

def v822_pa : Scalar.QComplex := ((999999497635475997798897683961 : Int)/10^30,(-1002361609218094120774744295 : Int)/10^30)
theorem v822_pa_checked : Scalar.distance (sourceCoefficient 8 83 1 0) v822_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v822_pb : Scalar.QComplex := ((-432496392341736367627344 : Int)/10^30,(-431477194550843434010470318 : Int)/10^30)
theorem v822_pb_checked : Scalar.distance (sourceCoefficient 8 83 1 1) v822_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v822_pg : Scalar.QComplex := ((-93086371301375592031231 : Int)/10^30,(93306251807670628437 : Int)/10^30)
theorem v822_pg_checked : Scalar.distance (sourceCoefficient 8 83 1 2) v822_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v822_mb : Scalar.QComplex := ((-804841617189486045093671 : Int)/10^30,(-431476660667256744279607116 : Int)/10^30)
theorem v822_mb_checked : Scalar.distance (sourceCoefficient 8 83 3 1) v822_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v822_mg : Scalar.QComplex := ((-93086256121972346758867 : Int)/10^30,(173635563044043723783 : Int)/10^30)
theorem v822_mg_checked : Scalar.distance (sourceCoefficient 8 83 3 2) v822_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v822_upper : Scalar.QComplex := ((999996278268488486864159213250 : Int)/10^30,(-2728268529991288795850796620 : Int)/10^30)
theorem v822_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 83 5) 1) 14) v822_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material822 : Material (8 : Basis) (83 : Basis) where
  plus := ![v822_pa,v822_pb,v822_pg]
  minus := ![(Primitive.Addresses.material822 1).one,v822_mb,v822_mg]
  upper := v822_upper
  lower := (Primitive.Addresses.material822 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v822_pa_checked.trans (by decide +kernel)
    · exact v822_pb_checked.trans (by decide +kernel)
    · exact v822_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 83 Primitive.Addresses.material822
    · exact v822_mb_checked.trans (by decide +kernel)
    · exact v822_mg_checked.trans (by decide +kernel)
  upper_error := v822_upper_checked
  lower_error := reuse_lower_error 8 83 Primitive.Addresses.material822

def v823_pa : Scalar.QComplex := ((999999461796057737420506945280 : Int)/10^30,(-1037500648125906241897396219 : Int)/10^30)
theorem v823_pa_checked : Scalar.distance (sourceCoefficient 8 84 1 0) v823_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v823_pb : Scalar.QComplex := ((-447658087317613416087715 : Int)/10^30,(-431477172756368598177364341 : Int)/10^30)
theorem v823_pb_checked : Scalar.distance (sourceCoefficient 8 84 1 1) v823_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v823_pg : Scalar.QComplex := ((-93086367282337212103923 : Int)/10^30,(96577218365350668174 : Int)/10^30)
theorem v823_pg_checked : Scalar.distance (sourceCoefficient 8 84 1 2) v823_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v823_mb : Scalar.QComplex := ((-820003287712320933727919 : Int)/10^30,(-431476625788930116736501951 : Int)/10^30)
theorem v823_mb_checked : Scalar.distance (sourceCoefficient 8 84 3 1) v823_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v823_mg : Scalar.QComplex := ((-93086249280238642890378 : Int)/10^30,(176906524915544312432 : Int)/10^30)
theorem v823_mg_checked : Scalar.distance (sourceCoefficient 8 84 3 2) v823_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v823_upper : Scalar.QComplex := ((999996181782330238913630335688 : Int)/10^30,(-2763407454708045594467533422 : Int)/10^30)
theorem v823_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 84 5) 1) 14) v823_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material823 : Material (8 : Basis) (84 : Basis) where
  plus := ![v823_pa,v823_pb,v823_pg]
  minus := ![(Primitive.Addresses.material823 1).one,v823_mb,v823_mg]
  upper := v823_upper
  lower := (Primitive.Addresses.material823 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v823_pa_checked.trans (by decide +kernel)
    · exact v823_pb_checked.trans (by decide +kernel)
    · exact v823_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 84 Primitive.Addresses.material823
    · exact v823_mb_checked.trans (by decide +kernel)
    · exact v823_mg_checked.trans (by decide +kernel)
  upper_error := v823_upper_checked
  lower_error := reuse_lower_error 8 84 Primitive.Addresses.material823

def v824_pa : Scalar.QComplex := ((999999376649569975339844086979 : Int)/10^30,(-1116557419698405703043173974 : Int)/10^30)
theorem v824_pa_checked : Scalar.distance (sourceCoefficient 8 85 1 0) v824_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v824_pb : Scalar.QComplex := ((-481769281334046589035615 : Int)/10^30,(-431477121125655083448410471 : Int)/10^30)
theorem v824_pb_checked : Scalar.distance (sourceCoefficient 8 85 1 1) v824_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v824_pg : Scalar.QComplex := ((-93086357749972525180379 : Int)/10^30,(103936328207186896299 : Int)/10^30)
theorem v824_pg_checked : Scalar.distance (sourceCoefficient 8 85 1 2) v824_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v824_mb : Scalar.QComplex := ((-854114424472617213581239 : Int)/10^30,(-431476544721811701447951131 : Int)/10^30)
theorem v824_mb_checked : Scalar.distance (sourceCoefficient 8 85 3 1) v824_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v824_mg : Scalar.QComplex := ((-93086233397297153800763 : Int)/10^30,(184265623791246215459 : Int)/10^30)
theorem v824_mg_checked : Scalar.distance (sourceCoefficient 8 85 3 2) v824_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v824_upper : Scalar.QComplex := ((999995960191153532683078608679 : Int)/10^30,(-2842463961579657010795230034 : Int)/10^30)
theorem v824_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 85 5) 1) 14) v824_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material824 : Material (8 : Basis) (85 : Basis) where
  plus := ![v824_pa,v824_pb,v824_pg]
  minus := ![(Primitive.Addresses.material824 1).one,v824_mb,v824_mg]
  upper := v824_upper
  lower := (Primitive.Addresses.material824 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v824_pa_checked.trans (by decide +kernel)
    · exact v824_pb_checked.trans (by decide +kernel)
    · exact v824_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 85 Primitive.Addresses.material824
    · exact v824_mb_checked.trans (by decide +kernel)
    · exact v824_mg_checked.trans (by decide +kernel)
  upper_error := v824_upper_checked
  lower_error := reuse_lower_error 8 85 Primitive.Addresses.material824

def v825_pa : Scalar.QComplex := ((999999360258621536257811775568 : Int)/10^30,(-1131142054588393887711312484 : Int)/10^30)
theorem v825_pa_checked : Scalar.distance (sourceCoefficient 8 86 1 0) v825_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v825_pb : Scalar.QComplex := ((-488062218313063002825414 : Int)/10^30,(-431477111207809614540777118 : Int)/10^30)
theorem v825_pb_checked : Scalar.distance (sourceCoefficient 8 86 1 1) v825_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v825_pg : Scalar.QComplex := ((-93086355917253178858199 : Int)/10^30,(105293959247290890390 : Int)/10^30)
theorem v825_pg_checked : Scalar.distance (sourceCoefficient 8 86 1 2) v825_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v825_mb : Scalar.QComplex := ((-860407350549831632166460 : Int)/10^30,(-431476529373448735876653892 : Int)/10^30)
theorem v825_mb_checked : Scalar.distance (sourceCoefficient 8 86 3 1) v825_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v825_mg : Scalar.QComplex := ((-93086230393004047706229 : Int)/10^30,(185623252744287873255 : Int)/10^30)
theorem v825_mg_checked : Scalar.distance (sourceCoefficient 8 86 3 2) v825_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v825_upper : Scalar.QComplex := ((999995918628472793615392764568 : Int)/10^30,(-2857048546458254727759291505 : Int)/10^30)
theorem v825_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 86 5) 1) 14) v825_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material825 : Material (8 : Basis) (86 : Basis) where
  plus := ![v825_pa,v825_pb,v825_pg]
  minus := ![(Primitive.Addresses.material825 1).one,v825_mb,v825_mg]
  upper := v825_upper
  lower := (Primitive.Addresses.material825 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v825_pa_checked.trans (by decide +kernel)
    · exact v825_pb_checked.trans (by decide +kernel)
    · exact v825_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 86 Primitive.Addresses.material825
    · exact v825_mb_checked.trans (by decide +kernel)
    · exact v825_mg_checked.trans (by decide +kernel)
  upper_error := v825_upper_checked
  lower_error := reuse_lower_error 8 86 Primitive.Addresses.material825

def v826_pa : Scalar.QComplex := ((999999359165747469561409935977 : Int)/10^30,(-1132107810410447598499316540 : Int)/10^30)
theorem v826_pa_checked : Scalar.distance (sourceCoefficient 8 87 1 0) v826_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v826_pb : Scalar.QComplex := ((-488478919897338410669837 : Int)/10^30,(-431477110546756282470703768 : Int)/10^30)
theorem v826_pb_checked : Scalar.distance (sourceCoefficient 8 87 1 1) v826_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v826_pg : Scalar.QComplex := ((-93086355795079888620740 : Int)/10^30,(105383857971841624830 : Int)/10^30)
theorem v826_pg_checked : Scalar.distance (sourceCoefficient 8 87 1 2) v826_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v826_mb : Scalar.QComplex := ((-860824051408490743142331 : Int)/10^30,(-431476528352800950259942564 : Int)/10^30)
theorem v826_mb_checked : Scalar.distance (sourceCoefficient 8 87 3 1) v826_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v826_mg : Scalar.QComplex := ((-93086230193252252560438 : Int)/10^30,(185713151329935156976 : Int)/10^30)
theorem v826_mg_checked : Scalar.distance (sourceCoefficient 8 87 3 2) v826_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v826_upper : Scalar.QComplex := ((999995915868793418445614428528 : Int)/10^30,(-2858014298955727092889138646 : Int)/10^30)
theorem v826_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 87 5) 1) 14) v826_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material826 : Material (8 : Basis) (87 : Basis) where
  plus := ![v826_pa,v826_pb,v826_pg]
  minus := ![(Primitive.Addresses.material826 1).one,v826_mb,v826_mg]
  upper := v826_upper
  lower := (Primitive.Addresses.material826 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v826_pa_checked.trans (by decide +kernel)
    · exact v826_pb_checked.trans (by decide +kernel)
    · exact v826_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 87 Primitive.Addresses.material826
    · exact v826_mb_checked.trans (by decide +kernel)
    · exact v826_mg_checked.trans (by decide +kernel)
  upper_error := v826_upper_checked
  lower_error := reuse_lower_error 8 87 Primitive.Addresses.material826

def v827_pa : Scalar.QComplex := ((999999345783475782514966950901 : Int)/10^30,(-1143867396351390682861784178 : Int)/10^30)
theorem v827_pa_checked : Scalar.distance (sourceCoefficient 8 88 1 0) v827_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v827_pb : Scalar.QComplex := ((-493552912660174727736148 : Int)/10^30,(-431477102454353595466946402 : Int)/10^30)
theorem v827_pb_checked : Scalar.distance (sourceCoefficient 8 88 1 1) v827_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v827_pg : Scalar.QComplex := ((-93086354299303424448117 : Int)/10^30,(106478515388191531440 : Int)/10^30)
theorem v827_pg_checked : Scalar.distance (sourceCoefficient 8 88 1 2) v827_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v827_mb : Scalar.QComplex := ((-865898035298668611082758 : Int)/10^30,(-431476515881774046250627927 : Int)/10^30)
theorem v827_mb_checked : Scalar.distance (sourceCoefficient 8 88 3 1) v827_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v827_mg : Scalar.QComplex := ((-93086227752836296563657 : Int)/10^30,(186807807047906357854 : Int)/10^30)
theorem v827_mg_checked : Scalar.distance (sourceCoefficient 8 88 3 2) v827_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v827_upper : Scalar.QComplex := ((999995882190563149956105300072 : Int)/10^30,(-2869773844285561394579822111 : Int)/10^30)
theorem v827_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 88 5) 1) 14) v827_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material827 : Material (8 : Basis) (88 : Basis) where
  plus := ![v827_pa,v827_pb,v827_pg]
  minus := ![(Primitive.Addresses.material827 1).one,v827_mb,v827_mg]
  upper := v827_upper
  lower := (Primitive.Addresses.material827 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v827_pa_checked.trans (by decide +kernel)
    · exact v827_pb_checked.trans (by decide +kernel)
    · exact v827_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 88 Primitive.Addresses.material827
    · exact v827_mb_checked.trans (by decide +kernel)
    · exact v827_mg_checked.trans (by decide +kernel)
  upper_error := v827_upper_checked
  lower_error := reuse_lower_error 8 88 Primitive.Addresses.material827

def v828_pa : Scalar.QComplex := ((999999327249803336828360195761 : Int)/10^30,(-1159956870204024512234982432 : Int)/10^30)
theorem v828_pa_checked : Scalar.distance (sourceCoefficient 8 89 1 0) v828_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v828_pb : Scalar.QComplex := ((-500495153043280304064879 : Int)/10^30,(-431477091253432347144352364 : Int)/10^30)
theorem v828_pb_checked : Scalar.distance (sourceCoefficient 8 89 1 1) v828_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v828_pg : Scalar.QComplex := ((-93086352228450215631274 : Int)/10^30,(107976226430650100851 : Int)/10^30)
theorem v828_pg_checked : Scalar.distance (sourceCoefficient 8 89 1 2) v828_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v828_mb : Scalar.QComplex := ((-872840263430970250185811 : Int)/10^30,(-431476498690016184822923821 : Int)/10^30)
theorem v828_mb_checked : Scalar.distance (sourceCoefficient 8 89 3 1) v828_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v828_mg : Scalar.QComplex := ((-93086224389526683579688 : Int)/10^30,(188305515745645605938 : Int)/10^30)
theorem v828_mg_checked : Scalar.distance (sourceCoefficient 8 89 3 2) v828_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v828_upper : Scalar.QComplex := ((999995835887946064017439757756 : Int)/10^30,(-2885863262187376643194199893 : Int)/10^30)
theorem v828_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 89 5) 1) 14) v828_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material828 : Material (8 : Basis) (89 : Basis) where
  plus := ![v828_pa,v828_pb,v828_pg]
  minus := ![(Primitive.Addresses.material828 1).one,v828_mb,v828_mg]
  upper := v828_upper
  lower := (Primitive.Addresses.material828 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v828_pa_checked.trans (by decide +kernel)
    · exact v828_pb_checked.trans (by decide +kernel)
    · exact v828_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 89 Primitive.Addresses.material828
    · exact v828_mb_checked.trans (by decide +kernel)
    · exact v828_mg_checked.trans (by decide +kernel)
  upper_error := v828_upper_checked
  lower_error := reuse_lower_error 8 89 Primitive.Addresses.material828

def v829_pa : Scalar.QComplex := ((999999296512224271914057834637 : Int)/10^30,(-1186159793856258342145560676 : Int)/10^30)
theorem v829_pa_checked : Scalar.distance (sourceCoefficient 8 90 1 0) v829_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v829_pb : Scalar.QComplex := ((-511801115645194960776124 : Int)/10^30,(-431477072693114508094786288 : Int)/10^30)
theorem v829_pb_checked : Scalar.distance (sourceCoefficient 8 90 1 1) v829_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v829_pg : Scalar.QComplex := ((-93086348795734358162662 : Int)/10^30,(110415361974237429725 : Int)/10^30)
theorem v829_pg_checked : Scalar.distance (sourceCoefficient 8 90 1 2) v829_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v829_mb : Scalar.QComplex := ((-884146205806439952772103 : Int)/10^30,(-431476470373168732828725264 : Int)/10^30)
theorem v829_mb_checked : Scalar.distance (sourceCoefficient 8 90 3 1) v829_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v829_mg : Scalar.QComplex := ((-93086218851947984739098 : Int)/10^30,(190744647418752116722 : Int)/10^30)
theorem v829_mg_checked : Scalar.distance (sourceCoefficient 8 90 3 2) v829_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v829_upper : Scalar.QComplex := ((999995759926543666025635661853 : Int)/10^30,(-2912066093763160730081387847 : Int)/10^30)
theorem v829_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 90 5) 1) 14) v829_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material829 : Material (8 : Basis) (90 : Basis) where
  plus := ![v829_pa,v829_pb,v829_pg]
  minus := ![(Primitive.Addresses.material829 1).one,v829_mb,v829_mg]
  upper := v829_upper
  lower := (Primitive.Addresses.material829 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v829_pa_checked.trans (by decide +kernel)
    · exact v829_pb_checked.trans (by decide +kernel)
    · exact v829_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 90 Primitive.Addresses.material829
    · exact v829_mb_checked.trans (by decide +kernel)
    · exact v829_mg_checked.trans (by decide +kernel)
  upper_error := v829_upper_checked
  lower_error := reuse_lower_error 8 90 Primitive.Addresses.material829

def v830_pa : Scalar.QComplex := ((999999278894290820764856372392 : Int)/10^30,(-1200920854330137143350237124 : Int)/10^30)
theorem v830_pa_checked : Scalar.distance (sourceCoefficient 8 91 1 0) v830_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v830_pb : Scalar.QComplex := ((-518170175652600376608549 : Int)/10^30,(-431477062063476984487873069 : Int)/10^30)
theorem v830_pb_checked : Scalar.distance (sourceCoefficient 8 91 1 1) v830_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v830_pg : Scalar.QComplex := ((-93086346829126610169235 : Int)/10^30,(111789415772492120741 : Int)/10^30)
theorem v830_pg_checked : Scalar.distance (sourceCoefficient 8 91 1 2) v830_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v830_mb : Scalar.QComplex := ((-890515254269454805655080 : Int)/10^30,(-431476454247323232545080314 : Int)/10^30)
theorem v830_mb_checked : Scalar.distance (sourceCoefficient 8 91 3 1) v830_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v830_mg : Scalar.QComplex := ((-93086215699594426195606 : Int)/10^30,(192118699008289867493 : Int)/10^30)
theorem v830_mg_checked : Scalar.distance (sourceCoefficient 8 91 3 2) v830_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v830_upper : Scalar.QComplex := ((999995716832385189749564979398 : Int)/10^30,(-2926827101845219061164653076 : Int)/10^30)
theorem v830_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 91 5) 1) 14) v830_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material830 : Material (8 : Basis) (91 : Basis) where
  plus := ![v830_pa,v830_pb,v830_pg]
  minus := ![(Primitive.Addresses.material830 1).one,v830_mb,v830_mg]
  upper := v830_upper
  lower := (Primitive.Addresses.material830 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v830_pa_checked.trans (by decide +kernel)
    · exact v830_pb_checked.trans (by decide +kernel)
    · exact v830_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 91 Primitive.Addresses.material830
    · exact v830_mb_checked.trans (by decide +kernel)
    · exact v830_mg_checked.trans (by decide +kernel)
  upper_error := v830_upper_checked
  lower_error := reuse_lower_error 8 91 Primitive.Addresses.material830

def v831_pa : Scalar.QComplex := ((999999240006942399797838653478 : Int)/10^30,(-1232876935306584735115857176 : Int)/10^30)
theorem v831_pa_checked : Scalar.distance (sourceCoefficient 8 92 1 0) v831_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v831_pb : Scalar.QComplex := ((-531958493316263440611022 : Int)/10^30,(-431477038622040013420116536 : Int)/10^30)
theorem v831_pb_checked : Scalar.distance (sourceCoefficient 8 92 1 1) v831_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v831_pg : Scalar.QComplex := ((-93086342490570954249325 : Int)/10^30,(114764091868587318048 : Int)/10^30)
theorem v831_pg_checked : Scalar.distance (sourceCoefficient 8 92 1 2) v831_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v831_mb : Scalar.QComplex := ((-904303546570192703326100 : Int)/10^30,(-431476418907197848829275249 : Int)/10^30)
theorem v831_mb_checked : Scalar.distance (sourceCoefficient 8 92 3 1) v831_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v831_mg : Scalar.QComplex := ((-93086208794028889226097 : Int)/10^30,(195093370252799075045 : Int)/10^30)
theorem v831_mg_checked : Scalar.distance (sourceCoefficient 8 92 3 2) v831_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v831_upper : Scalar.QComplex := ((999995622791797954591628219446 : Int)/10^30,(-2958783068110802321576661154 : Int)/10^30)
theorem v831_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 92 5) 1) 14) v831_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material831 : Material (8 : Basis) (92 : Basis) where
  plus := ![v831_pa,v831_pb,v831_pg]
  minus := ![(Primitive.Addresses.material831 1).one,v831_mb,v831_mg]
  upper := v831_upper
  lower := (Primitive.Addresses.material831 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v831_pa_checked.trans (by decide +kernel)
    · exact v831_pb_checked.trans (by decide +kernel)
    · exact v831_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 92 Primitive.Addresses.material831
    · exact v831_mb_checked.trans (by decide +kernel)
    · exact v831_mg_checked.trans (by decide +kernel)
  upper_error := v831_upper_checked
  lower_error := reuse_lower_error 8 92 Primitive.Addresses.material831

def v832_pa : Scalar.QComplex := ((999999192530155023935841494127 : Int)/10^30,(-1270802517287630246431094580 : Int)/10^30)
theorem v832_pa_checked : Scalar.distance (sourceCoefficient 8 93 1 0) v832_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v832_pb : Scalar.QComplex := ((-548322513263578240999501 : Int)/10^30,(-431477010039300717284572053 : Int)/10^30)
theorem v832_pb_checked : Scalar.distance (sourceCoefficient 8 93 1 1) v832_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v832_pg : Scalar.QComplex := ((-93086337197646061077161 : Int)/10^30,(118294447155052692819 : Int)/10^30)
theorem v832_pg_checked : Scalar.distance (sourceCoefficient 8 93 1 2) v832_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v832_mb : Scalar.QComplex := ((-920667535758818310897430 : Int)/10^30,(-431476376203056988920594087 : Int)/10^30)
theorem v832_mb_checked : Scalar.distance (sourceCoefficient 8 93 3 1) v832_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v832_mg : Scalar.QComplex := ((-93086200454568355931847 : Int)/10^30,(198623719657196033138 : Int)/10^30)
theorem v832_mg_checked : Scalar.distance (sourceCoefficient 8 93 3 2) v832_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v832_upper : Scalar.QComplex := ((999995509858967372463829080400 : Int)/10^30,(-2996708511665520573702444735 : Int)/10^30)
theorem v832_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 93 5) 1) 14) v832_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material832 : Material (8 : Basis) (93 : Basis) where
  plus := ![v832_pa,v832_pb,v832_pg]
  minus := ![(Primitive.Addresses.material832 1).one,v832_mb,v832_mg]
  upper := v832_upper
  lower := (Primitive.Addresses.material832 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v832_pa_checked.trans (by decide +kernel)
    · exact v832_pb_checked.trans (by decide +kernel)
    · exact v832_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 93 Primitive.Addresses.material832
    · exact v832_mb_checked.trans (by decide +kernel)
    · exact v832_mg_checked.trans (by decide +kernel)
  upper_error := v832_upper_checked
  lower_error := reuse_lower_error 8 93 Primitive.Addresses.material832

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
