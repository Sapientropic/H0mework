import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B184
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B185

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4433_pa : Scalar.QComplex := ((999997915448658075670135171650 : Int)/10^30,(-2041837000961233097991742547 : Int)/10^30)
theorem v4433_pa_checked : Scalar.distance (sourceCoefficient 72 78 1 0) v4433_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4433_pb : Scalar.QComplex := ((-881006766793038362756613 : Int)/10^30,(-431476621235902175625068207 : Int)/10^30)
theorem v4433_pb_checked : Scalar.distance (sourceCoefficient 72 78 1 1) v4433_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4433_pg : Scalar.QComplex := ((-93086235818184347724395 : Int)/10^30,(190067316778851892153 : Int)/10^30)
theorem v4433_pg_checked : Scalar.distance (sourceCoefficient 72 78 1 2) v4433_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4433_mb : Scalar.QComplex := ((-1253351329894904535713827 : Int)/10^30,(-431475700308275963175197147 : Int)/10^30)
theorem v4433_mb_checked : Scalar.distance (sourceCoefficient 72 78 3 1) v4433_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4433_mg : Scalar.QComplex := ((-93086037138390435497938 : Int)/10^30,(270396475070766192180 : Int)/10^30)
theorem v4433_mg_checked : Scalar.distance (sourceCoefficient 72 78 3 2) v4433_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4433_upper : Scalar.QComplex := ((999992902043801368390181880571 : Int)/10^30,(-3767739642847024261904739761 : Int)/10^30)
theorem v4433_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 72 78 5) 1) 14) v4433_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4433 : Material (72 : Basis) (78 : Basis) where
  plus := ![v4433_pa,v4433_pb,v4433_pg]
  minus := ![(Primitive.Addresses.material4433 1).one,v4433_mb,v4433_mg]
  upper := v4433_upper
  lower := (Primitive.Addresses.material4433 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4433_pa_checked.trans (by decide +kernel)
    · exact v4433_pb_checked.trans (by decide +kernel)
    · exact v4433_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 72 78 Primitive.Addresses.material4433
    · exact v4433_mb_checked.trans (by decide +kernel)
    · exact v4433_mg_checked.trans (by decide +kernel)
  upper_error := v4433_upper_checked
  lower_error := reuse_lower_error 72 78 Primitive.Addresses.material4433

def v4434_pa : Scalar.QComplex := ((999997904045615705616421917183 : Int)/10^30,(-2047414070373647235211552426 : Int)/10^30)
theorem v4434_pa_checked : Scalar.distance (sourceCoefficient 72 79 1 0) v4434_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4434_pb : Scalar.QComplex := ((-883413146760284766490614 : Int)/10^30,(-431476616259361071134131086 : Int)/10^30)
theorem v4434_pb_checked : Scalar.distance (sourceCoefficient 72 79 1 1) v4434_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4434_pg : Scalar.QComplex := ((-93086234750633665967819 : Int)/10^30,(190586466247091241133 : Int)/10^30)
theorem v4434_pg_checked : Scalar.distance (sourceCoefficient 72 79 1 2) v4434_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4434_mb : Scalar.QComplex := ((-1255757704671614862559897 : Int)/10^30,(-431475693255139179274800886 : Int)/10^30)
theorem v4434_mb_checked : Scalar.distance (sourceCoefficient 72 79 3 1) v4434_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4434_mg : Scalar.QComplex := ((-93086035622837541772796 : Int)/10^30,(270915623424454310175 : Int)/10^30)
theorem v4434_mg_checked : Scalar.distance (sourceCoefficient 72 79 3 2) v4434_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4434_upper : Scalar.QComplex := ((999992881015260123786629536780 : Int)/10^30,(-3773316684272431983137367844 : Int)/10^30)
theorem v4434_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 72 79 5) 1) 14) v4434_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4434 : Material (72 : Basis) (79 : Basis) where
  plus := ![v4434_pa,v4434_pb,v4434_pg]
  minus := ![(Primitive.Addresses.material4434 1).one,v4434_mb,v4434_mg]
  upper := v4434_upper
  lower := (Primitive.Addresses.material4434 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4434_pa_checked.trans (by decide +kernel)
    · exact v4434_pb_checked.trans (by decide +kernel)
    · exact v4434_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 72 79 Primitive.Addresses.material4434
    · exact v4434_mb_checked.trans (by decide +kernel)
    · exact v4434_mg_checked.trans (by decide +kernel)
  upper_error := v4434_upper_checked
  lower_error := reuse_lower_error 72 79 Primitive.Addresses.material4434

def v4435_pa : Scalar.QComplex := ((999997886170693875711177163116 : Int)/10^30,(-2056126003914702260575598675 : Int)/10^30)
theorem v4435_pa_checked : Scalar.distance (sourceCoefficient 72 80 1 0) v4435_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4435_pb : Scalar.QComplex := ((-887172150044848121149270 : Int)/10^30,(-431476608449703629335443485 : Int)/10^30)
theorem v4435_pb_checked : Scalar.distance (sourceCoefficient 72 80 1 1) v4435_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4435_pg : Scalar.QComplex := ((-93086233076254389724478 : Int)/10^30,(191397429016046091340 : Int)/10^30)
theorem v4435_pg_checked : Scalar.distance (sourceCoefficient 72 80 1 2) v4435_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4435_mb : Scalar.QComplex := ((-1259516699817146861080605 : Int)/10^30,(-431475682201634110013576925 : Int)/10^30)
theorem v4435_mb_checked : Scalar.distance (sourceCoefficient 72 80 3 1) v4435_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4435_mg : Scalar.QComplex := ((-93086033248634543776610 : Int)/10^30,(271726584446536754515 : Int)/10^30)
theorem v4435_mg_checked : Scalar.distance (sourceCoefficient 72 80 3 2) v4435_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4435_upper : Scalar.QComplex := ((999992848104357965053784657658 : Int)/10^30,(-3782028573987591896526611916 : Int)/10^30)
theorem v4435_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 72 80 5) 1) 14) v4435_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4435 : Material (72 : Basis) (80 : Basis) where
  plus := ![v4435_pa,v4435_pb,v4435_pg]
  minus := ![(Primitive.Addresses.material4435 1).one,v4435_mb,v4435_mg]
  upper := v4435_upper
  lower := (Primitive.Addresses.material4435 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4435_pa_checked.trans (by decide +kernel)
    · exact v4435_pb_checked.trans (by decide +kernel)
    · exact v4435_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 72 80 Primitive.Addresses.material4435
    · exact v4435_mb_checked.trans (by decide +kernel)
    · exact v4435_mg_checked.trans (by decide +kernel)
  upper_error := v4435_upper_checked
  lower_error := reuse_lower_error 72 80 Primitive.Addresses.material4435

def v4436_pa : Scalar.QComplex := ((999997831890048010672829620708 : Int)/10^30,(-2082358087188149881966150034 : Int)/10^30)
theorem v4436_pa_checked : Scalar.distance (sourceCoefficient 72 81 1 0) v4436_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4436_pb : Scalar.QComplex := ((-898490703548077992303460 : Int)/10^30,(-431476584670741882515778536 : Int)/10^30)
theorem v4436_pb_checked : Scalar.distance (sourceCoefficient 72 81 1 1) v4436_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4436_pg : Scalar.QComplex := ((-93086227984836636026835 : Int)/10^30,(193839279914936315231 : Int)/10^30)
theorem v4436_pg_checked : Scalar.distance (sourceCoefficient 72 81 1 2) v4436_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4436_mb : Scalar.QComplex := ((-1270835228585788956708523 : Int)/10^30,(-431475648655279312627024596 : Int)/10^30)
theorem v4436_mb_checked : Scalar.distance (sourceCoefficient 72 81 3 1) v4436_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4436_mg : Scalar.QComplex := ((-93086026050011336986174 : Int)/10^30,(274168430042550078152 : Int)/10^30)
theorem v4436_mg_checked : Scalar.distance (sourceCoefficient 72 81 3 2) v4436_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4436_upper : Scalar.QComplex := ((999992748549596970695539426022 : Int)/10^30,(-3808260524507962457747525155 : Int)/10^30)
theorem v4436_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 72 81 5) 1) 14) v4436_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4436 : Material (72 : Basis) (81 : Basis) where
  plus := ![v4436_pa,v4436_pb,v4436_pg]
  minus := ![(Primitive.Addresses.material4436 1).one,v4436_mb,v4436_mg]
  upper := v4436_upper
  lower := (Primitive.Addresses.material4436 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4436_pa_checked.trans (by decide +kernel)
    · exact v4436_pb_checked.trans (by decide +kernel)
    · exact v4436_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 72 81 Primitive.Addresses.material4436
    · exact v4436_mb_checked.trans (by decide +kernel)
    · exact v4436_mg_checked.trans (by decide +kernel)
  upper_error := v4436_upper_checked
  lower_error := reuse_lower_error 72 81 Primitive.Addresses.material4436

def v4437_pa : Scalar.QComplex := ((999997811141465226810272438421 : Int)/10^30,(-2092298324437673062318186113 : Int)/10^30)
theorem v4437_pa_checked : Scalar.distance (sourceCoefficient 72 82 1 0) v4437_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4437_pb : Scalar.QComplex := ((-902779692128312993031728 : Int)/10^30,(-431476575556647620733258334 : Int)/10^30)
theorem v4437_pb_checked : Scalar.distance (sourceCoefficient 72 82 1 1) v4437_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4437_pg : Scalar.QComplex := ((-93086226035999142477642 : Int)/10^30,(194764581075463061632 : Int)/10^30)
theorem v4437_pg_checked : Scalar.distance (sourceCoefficient 72 82 1 2) v4437_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4437_mb : Scalar.QComplex := ((-1275124207703984628203143 : Int)/10^30,(-431475635839984468570415197 : Int)/10^30)
theorem v4437_mb_checked : Scalar.distance (sourceCoefficient 72 82 3 1) v4437_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4437_mg : Scalar.QComplex := ((-93086023302681341560923 : Int)/10^30,(275093729176785929587 : Int)/10^30)
theorem v4437_mg_checked : Scalar.distance (sourceCoefficient 72 82 3 2) v4437_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4437_upper : Scalar.QComplex := ((999992710645097368011755862951 : Int)/10^30,(-3818200711142498329005598546 : Int)/10^30)
theorem v4437_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 72 82 5) 1) 14) v4437_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4437 : Material (72 : Basis) (82 : Basis) where
  plus := ![v4437_pa,v4437_pb,v4437_pg]
  minus := ![(Primitive.Addresses.material4437 1).one,v4437_mb,v4437_mg]
  upper := v4437_upper
  lower := (Primitive.Addresses.material4437 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4437_pa_checked.trans (by decide +kernel)
    · exact v4437_pb_checked.trans (by decide +kernel)
    · exact v4437_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 72 82 Primitive.Addresses.material4437
    · exact v4437_mb_checked.trans (by decide +kernel)
    · exact v4437_mg_checked.trans (by decide +kernel)
  upper_error := v4437_upper_checked
  lower_error := reuse_lower_error 72 82 Primitive.Addresses.material4437

def v4438_pa : Scalar.QComplex := ((999997782659809089720132245739 : Int)/10^30,(-2105866915363608040335241511 : Int)/10^30)
theorem v4438_pa_checked : Scalar.distance (sourceCoefficient 72 83 1 0) v4438_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4438_pb : Scalar.QComplex := ((-908634233578246507333725 : Int)/10^30,(-431476563023999648048529553 : Int)/10^30)
theorem v4438_pb_checked : Scalar.distance (sourceCoefficient 72 83 1 1) v4438_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4438_pg : Scalar.QComplex := ((-93086223358482266402697 : Int)/10^30,(196027632706723418306 : Int)/10^30)
theorem v4438_pg_checked : Scalar.distance (sourceCoefficient 72 83 1 2) v4438_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4438_mb : Scalar.QComplex := ((-1280978736158894044017032 : Int)/10^30,(-431475618255135569829363495 : Int)/10^30)
theorem v4438_mb_checked : Scalar.distance (sourceCoefficient 72 83 3 1) v4438_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4438_mg : Scalar.QComplex := ((-93086019535208790403966 : Int)/10^30,(276356778027177966462 : Int)/10^30)
theorem v4438_mg_checked : Scalar.distance (sourceCoefficient 72 83 3 2) v4438_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4438_upper : Scalar.QComplex := ((999992658745326645792249731282 : Int)/10^30,(-3831769232702856344539891598 : Int)/10^30)
theorem v4438_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 72 83 5) 1) 14) v4438_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4438 : Material (72 : Basis) (83 : Basis) where
  plus := ![v4438_pa,v4438_pb,v4438_pg]
  minus := ![(Primitive.Addresses.material4438 1).one,v4438_mb,v4438_mg]
  upper := v4438_upper
  lower := (Primitive.Addresses.material4438 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4438_pa_checked.trans (by decide +kernel)
    · exact v4438_pb_checked.trans (by decide +kernel)
    · exact v4438_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 72 83 Primitive.Addresses.material4438
    · exact v4438_mb_checked.trans (by decide +kernel)
    · exact v4438_mg_checked.trans (by decide +kernel)
  upper_error := v4438_upper_checked
  lower_error := reuse_lower_error 72 83 Primitive.Addresses.material4438

def v4439_pa : Scalar.QComplex := ((999997708044255837860893834982 : Int)/10^30,(-2141005893327513709790130772 : Int)/10^30)
theorem v4439_pa_checked : Scalar.distance (sourceCoefficient 72 84 1 0) v4439_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4439_pb : Scalar.QComplex := ((-923795911023507428031911 : Int)/10^30,(-431476530075505142551841368 : Int)/10^30)
theorem v4439_pb_checked : Scalar.distance (sourceCoefficient 72 84 1 1) v4439_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4439_pg : Scalar.QComplex := ((-93086216331500685691996 : Int)/10^30,(199298594536861373842 : Int)/10^30)
theorem v4439_pg_checked : Scalar.distance (sourceCoefficient 72 84 1 2) v4439_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4439_mb : Scalar.QComplex := ((-1296140379525702715816498 : Int)/10^30,(-431475572222808553906131637 : Int)/10^30)
theorem v4439_mb_checked : Scalar.distance (sourceCoefficient 72 84 3 1) v4439_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4439_mg : Scalar.QComplex := ((-93086009685537085402705 : Int)/10^30,(279627732575418721645 : Int)/10^30)
theorem v4439_mg_checked : Scalar.distance (sourceCoefficient 72 84 3 2) v4439_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4439_upper : Scalar.QComplex := ((999992523483196342512725781227 : Int)/10^30,(-3866908029551706208469931300 : Int)/10^30)
theorem v4439_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 72 84 5) 1) 14) v4439_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4439 : Material (72 : Basis) (84 : Basis) where
  plus := ![v4439_pa,v4439_pb,v4439_pg]
  minus := ![(Primitive.Addresses.material4439 1).one,v4439_mb,v4439_mg]
  upper := v4439_upper
  lower := (Primitive.Addresses.material4439 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4439_pa_checked.trans (by decide +kernel)
    · exact v4439_pb_checked.trans (by decide +kernel)
    · exact v4439_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 72 84 Primitive.Addresses.material4439
    · exact v4439_mb_checked.trans (by decide +kernel)
    · exact v4439_mg_checked.trans (by decide +kernel)
  upper_error := v4439_upper_checked
  lower_error := reuse_lower_error 72 84 Primitive.Addresses.material4439

def v4440_pa : Scalar.QComplex := ((999997535658160926813564880310 : Int)/10^30,(-2220062522805534200846210483 : Int)/10^30)
theorem v4440_pa_checked : Scalar.distance (sourceCoefficient 72 85 1 0) v4440_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4440_pb : Scalar.QComplex := ((-957907064166227546408689 : Int)/10^30,(-431476453350173864057195599 : Int)/10^30)
theorem v4440_pb_checked : Scalar.distance (sourceCoefficient 72 85 1 1) v4440_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4440_pg : Scalar.QComplex := ((-93086200031783298393341 : Int)/10^30,(206657693356141531237 : Int)/10^30)
theorem v4440_pg_checked : Scalar.distance (sourceCoefficient 72 85 1 2) v4440_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4440_mb : Scalar.QComplex := ((-1330251453756776249748650 : Int)/10^30,(-431475466061116990898445452 : Int)/10^30)
theorem v4440_mb_checked : Scalar.distance (sourceCoefficient 72 85 3 1) v4440_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4440_mg : Scalar.QComplex := ((-93085987035254927702124 : Int)/10^30,(286986814588648067973 : Int)/10^30)
theorem v4440_mg_checked : Scalar.distance (sourceCoefficient 72 85 3 2) v4440_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4440_upper : Scalar.QComplex := ((999992214652787662642464152738 : Int)/10^30,(-3945964243761402663963615716 : Int)/10^30)
theorem v4440_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 72 85 5) 1) 14) v4440_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4440 : Material (72 : Basis) (85 : Basis) where
  plus := ![v4440_pa,v4440_pb,v4440_pg]
  minus := ![(Primitive.Addresses.material4440 1).one,v4440_mb,v4440_mg]
  upper := v4440_upper
  lower := (Primitive.Addresses.material4440 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4440_pa_checked.trans (by decide +kernel)
    · exact v4440_pb_checked.trans (by decide +kernel)
    · exact v4440_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 72 85 Primitive.Addresses.material4440
    · exact v4440_mb_checked.trans (by decide +kernel)
    · exact v4440_mg_checked.trans (by decide +kernel)
  upper_error := v4440_upper_checked
  lower_error := reuse_lower_error 72 85 Primitive.Addresses.material4440

def v4441_pa : Scalar.QComplex := ((999997503172983492086965354240 : Int)/10^30,(-2234647130727953590810414497 : Int)/10^30)
theorem v4441_pa_checked : Scalar.distance (sourceCoefficient 72 86 1 0) v4441_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4441_pb : Scalar.QComplex := ((-964199993387978026577719 : Int)/10^30,(-431476438802796751067575609 : Int)/10^30)
theorem v4441_pb_checked : Scalar.distance (sourceCoefficient 72 86 1 1) v4441_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4441_pg : Scalar.QComplex := ((-93086196950602076339763 : Int)/10^30,(208015322304316690009 : Int)/10^30)
theorem v4441_pg_checked : Scalar.distance (sourceCoefficient 72 86 1 2) v4441_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4441_mb : Scalar.QComplex := ((-1336544368081650320620109 : Int)/10^30,(-431475446083230799202499143 : Int)/10^30)
theorem v4441_mb_checked : Scalar.distance (sourceCoefficient 72 86 3 1) v4441_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4441_mg : Scalar.QComplex := ((-93085982782502215975974 : Int)/10^30,(288344440372395299249 : Int)/10^30)
theorem v4441_mg_checked : Scalar.distance (sourceCoefficient 72 86 3 2) v4441_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4441_upper : Scalar.QComplex := ((999992156995948441971000092837 : Int)/10^30,(-3960548773895292561816251344 : Int)/10^30)
theorem v4441_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 72 86 5) 1) 14) v4441_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4441 : Material (72 : Basis) (86 : Basis) where
  plus := ![v4441_pa,v4441_pb,v4441_pg]
  minus := ![(Primitive.Addresses.material4441 1).one,v4441_mb,v4441_mg]
  upper := v4441_upper
  lower := (Primitive.Addresses.material4441 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4441_pa_checked.trans (by decide +kernel)
    · exact v4441_pb_checked.trans (by decide +kernel)
    · exact v4441_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 72 86 Primitive.Addresses.material4441
    · exact v4441_mb_checked.trans (by decide +kernel)
    · exact v4441_mg_checked.trans (by decide +kernel)
  upper_error := v4441_upper_checked
  lower_error := reuse_lower_error 72 86 Primitive.Addresses.material4441

def v4442_pa : Scalar.QComplex := ((999997501014392291943551372584 : Int)/10^30,(-2235612884756000274660945645 : Int)/10^30)
theorem v4442_pa_checked : Scalar.distance (sourceCoefficient 72 87 1 0) v4442_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4442_pb : Scalar.QComplex := ((-964616694456204335450443 : Int)/10^30,(-431476437835188119699043904 : Int)/10^30)
theorem v4442_pb_checked : Scalar.distance (sourceCoefficient 72 87 1 1) v4442_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4442_pg : Scalar.QComplex := ((-93086196745758953904692 : Int)/10^30,(208105220889702672288 : Int)/10^30)
theorem v4442_pg_checked : Scalar.distance (sourceCoefficient 72 87 1 2) v4442_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4442_mb : Scalar.QComplex := ((-1336961068159717108216526 : Int)/10^30,(-431475444756028273759008082 : Int)/10^30)
theorem v4442_mb_checked : Scalar.distance (sourceCoefficient 72 87 3 1) v4442_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4442_mg : Scalar.QComplex := ((-93085982500080739507241 : Int)/10^30,(288434338747537540751 : Int)/10^30)
theorem v4442_mg_checked : Scalar.distance (sourceCoefficient 72 87 3 2) v4442_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4442_upper : Scalar.QComplex := ((999992153170556616908069403527 : Int)/10^30,(-3961514522759429480744925356 : Int)/10^30)
theorem v4442_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 72 87 5) 1) 14) v4442_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4442 : Material (72 : Basis) (87 : Basis) where
  plus := ![v4442_pa,v4442_pb,v4442_pg]
  minus := ![(Primitive.Addresses.material4442 1).one,v4442_mb,v4442_mg]
  upper := v4442_upper
  lower := (Primitive.Addresses.material4442 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4442_pa_checked.trans (by decide +kernel)
    · exact v4442_pb_checked.trans (by decide +kernel)
    · exact v4442_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 72 87 Primitive.Addresses.material4442
    · exact v4442_mb_checked.trans (by decide +kernel)
    · exact v4442_mg_checked.trans (by decide +kernel)
  upper_error := v4442_upper_checked
  lower_error := reuse_lower_error 72 87 Primitive.Addresses.material4442

def v4443_pa : Scalar.QComplex := ((999997474655349573003696380132 : Int)/10^30,(-2247372448769537880887864738 : Int)/10^30)
theorem v4443_pa_checked : Scalar.distance (sourceCoefficient 72 88 1 0) v4443_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4443_pb : Scalar.QComplex := ((-969690680911586078176890 : Int)/10^30,(-431476426009995747116468339 : Int)/10^30)
theorem v4443_pb_checked : Scalar.distance (sourceCoefficient 72 88 1 1) v4443_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4443_pg : Scalar.QComplex := ((-93086194243348131199535 : Int)/10^30,(209199876605099404664 : Int)/10^30)
theorem v4443_pg_checked : Scalar.distance (sourceCoefficient 72 88 1 2) v4443_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4443_mb : Scalar.QComplex := ((-1342035042521213370322754 : Int)/10^30,(-431475428552218517108292550 : Int)/10^30)
theorem v4443_mb_checked : Scalar.distance (sourceCoefficient 72 88 3 1) v4443_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4443_mg : Scalar.QComplex := ((-93085979053032267639885 : Int)/10^30,(289528991895876086452 : Int)/10^30)
theorem v4443_mg_checked : Scalar.distance (sourceCoefficient 72 88 3 2) v4443_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4443_upper : Scalar.QComplex := ((999992106515612488613858243233 : Int)/10^30,(-3973274023765161405018608884 : Int)/10^30)
theorem v4443_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 72 88 5) 1) 14) v4443_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4443 : Material (72 : Basis) (88 : Basis) where
  plus := ![v4443_pa,v4443_pb,v4443_pg]
  minus := ![(Primitive.Addresses.material4443 1).one,v4443_mb,v4443_mg]
  upper := v4443_upper
  lower := (Primitive.Addresses.material4443 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4443_pa_checked.trans (by decide +kernel)
    · exact v4443_pb_checked.trans (by decide +kernel)
    · exact v4443_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 72 88 Primitive.Addresses.material4443
    · exact v4443_mb_checked.trans (by decide +kernel)
    · exact v4443_mg_checked.trans (by decide +kernel)
  upper_error := v4443_upper_checked
  lower_error := reuse_lower_error 72 88 Primitive.Addresses.material4443

def v4444_pa : Scalar.QComplex := ((999997438366849903493333721587 : Int)/10^30,(-2263461892373851665240496616 : Int)/10^30)
theorem v4444_pa_checked : Scalar.distance (sourceCoefficient 72 89 1 0) v4444_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4444_pb : Scalar.QComplex := ((-976632912593712215719882 : Int)/10^30,(-431476409701869045685513955 : Int)/10^30)
theorem v4444_pb_checked : Scalar.distance (sourceCoefficient 72 89 1 1) v4444_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4444_pg : Scalar.QComplex := ((-93086190795217089190692 : Int)/10^30,(210697585301134637363 : Int)/10^30)
theorem v4444_pg_checked : Scalar.distance (sourceCoefficient 72 89 1 2) v4444_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4444_mb : Scalar.QComplex := ((-1348977257545250524374717 : Int)/10^30,(-431475406253264612771607216 : Int)/10^30)
theorem v4444_mb_checked : Scalar.distance (sourceCoefficient 72 89 3 1) v4444_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4444_mg : Scalar.QComplex := ((-93085974312447359145058 : Int)/10^30,(291026697058664131752 : Int)/10^30)
theorem v4444_mg_checked : Scalar.distance (sourceCoefficient 72 89 3 2) v4444_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4444_upper : Scalar.QComplex := ((999992042458246828437249716668 : Int)/10^30,(-3989363380775480576955713022 : Int)/10^30)
theorem v4444_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 72 89 5) 1) 14) v4444_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4444 : Material (72 : Basis) (89 : Basis) where
  plus := ![v4444_pa,v4444_pb,v4444_pg]
  minus := ![(Primitive.Addresses.material4444 1).one,v4444_mb,v4444_mg]
  upper := v4444_upper
  lower := (Primitive.Addresses.material4444 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4444_pa_checked.trans (by decide +kernel)
    · exact v4444_pb_checked.trans (by decide +kernel)
    · exact v4444_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 72 89 Primitive.Addresses.material4444
    · exact v4444_mb_checked.trans (by decide +kernel)
    · exact v4444_mg_checked.trans (by decide +kernel)
  upper_error := v4444_upper_checked
  lower_error := reuse_lower_error 72 89 Primitive.Addresses.material4444

def v4445_pa : Scalar.QComplex := ((999997378714193749203694806692 : Int)/10^30,(-2289664766152965581005056055 : Int)/10^30)
theorem v4445_pa_checked : Scalar.distance (sourceCoefficient 72 90 1 0) v4445_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4445_pb : Scalar.QComplex := ((-987938860849541245876258 : Int)/10^30,(-431476382824081427911804073 : Int)/10^30)
theorem v4445_pb_checked : Scalar.distance (sourceCoefficient 72 90 1 1) v4445_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4445_pg : Scalar.QComplex := ((-93086185119500264555182 : Int)/10^30,(213136716975963237656 : Int)/10^30)
theorem v4445_pg_checked : Scalar.distance (sourceCoefficient 72 90 1 2) v4445_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4445_mb : Scalar.QComplex := ((-1360283178397038128003376 : Int)/10^30,(-431475369618962859053162625 : Int)/10^30)
theorem v4445_mb_checked : Scalar.distance (sourceCoefficient 72 90 3 1) v4445_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4445_mg : Scalar.QComplex := ((-93085966531871866873880 : Int)/10^30,(293465822927404540818 : Int)/10^30)
theorem v4445_mg_checked : Scalar.distance (sourceCoefficient 72 90 3 2) v4445_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4445_upper : Scalar.QComplex := ((999991937581896483161347858767 : Int)/10^30,(-4015566112573419128891238615 : Int)/10^30)
theorem v4445_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 72 90 5) 1) 14) v4445_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4445 : Material (72 : Basis) (90 : Basis) where
  plus := ![v4445_pa,v4445_pb,v4445_pg]
  minus := ![(Primitive.Addresses.material4445 1).one,v4445_mb,v4445_mg]
  upper := v4445_upper
  lower := (Primitive.Addresses.material4445 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4445_pa_checked.trans (by decide +kernel)
    · exact v4445_pb_checked.trans (by decide +kernel)
    · exact v4445_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 72 90 Primitive.Addresses.material4445
    · exact v4445_mb_checked.trans (by decide +kernel)
    · exact v4445_mg_checked.trans (by decide +kernel)
  upper_error := v4445_upper_checked
  lower_error := reuse_lower_error 72 90 Primitive.Addresses.material4445

def v4446_pa : Scalar.QComplex := ((999997344807345276036638930965 : Int)/10^30,(-2304425798197870597265984303 : Int)/10^30)
theorem v4446_pa_checked : Scalar.distance (sourceCoefficient 72 91 1 0) v4446_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4446_pb : Scalar.QComplex := ((-994307912679305248772886 : Int)/10^30,(-431476367508910556911100855 : Int)/10^30)
theorem v4446_pb_checked : Scalar.distance (sourceCoefficient 72 91 1 1) v4446_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4446_pg : Scalar.QComplex := ((-93086181889328461102651 : Int)/10^30,(214510768568924968470 : Int)/10^30)
theorem v4446_pg_checked : Scalar.distance (sourceCoefficient 72 91 1 2) v4446_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4446_mb : Scalar.QComplex := ((-1366652214639010362647568 : Int)/10^30,(-431475348807592812950164430 : Int)/10^30)
theorem v4446_mb_checked : Scalar.distance (sourceCoefficient 72 91 3 1) v4446_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4446_mg : Scalar.QComplex := ((-93085962115956626422432 : Int)/10^30,(294839871221251281470 : Int)/10^30)
theorem v4446_mg_checked : Scalar.distance (sourceCoefficient 72 91 3 2) v4446_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4446_upper : Scalar.QComplex := ((999991878198896311122614146408 : Int)/10^30,(-4030327064113356407472381208 : Int)/10^30)
theorem v4446_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 72 91 5) 1) 14) v4446_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4446 : Material (72 : Basis) (91 : Basis) where
  plus := ![v4446_pa,v4446_pb,v4446_pg]
  minus := ![(Primitive.Addresses.material4446 1).one,v4446_mb,v4446_mg]
  upper := v4446_upper
  lower := (Primitive.Addresses.material4446 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4446_pa_checked.trans (by decide +kernel)
    · exact v4446_pb_checked.trans (by decide +kernel)
    · exact v4446_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 72 91 Primitive.Addresses.material4446
    · exact v4446_mb_checked.trans (by decide +kernel)
    · exact v4446_mg_checked.trans (by decide +kernel)
  upper_error := v4446_upper_checked
  lower_error := reuse_lower_error 72 91 Primitive.Addresses.material4446

def v4447_pa : Scalar.QComplex := ((999997270656278392936799093247 : Int)/10^30,(-2336381816804987832791664672 : Int)/10^30)
theorem v4447_pa_checked : Scalar.distance (sourceCoefficient 72 92 1 0) v4447_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4447_pb : Scalar.QComplex := ((-1008096212402327168765914 : Int)/10^30,(-431476333923806687283171014 : Int)/10^30)
theorem v4447_pb_checked : Scalar.distance (sourceCoefficient 72 92 1 1) v4447_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4447_pg : Scalar.QComplex := ((-93086174815294908742442 : Int)/10^30,(217485439826905154105 : Int)/10^30)
theorem v4447_pg_checked : Scalar.distance (sourceCoefficient 72 92 1 2) v4447_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4447_mb : Scalar.QComplex := ((-1380440480245586116770239 : Int)/10^30,(-431475303323819789590251668 : Int)/10^30)
theorem v4447_mb_checked : Scalar.distance (sourceCoefficient 72 92 3 1) v4447_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4447_mg : Scalar.QComplex := ((-93085952474918386631416 : Int)/10^30,(297814535267053055524 : Int)/10^30)
theorem v4447_mg_checked : Scalar.distance (sourceCoefficient 72 92 3 2) v4447_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4447_upper : Scalar.QComplex := ((999991748894750778804230677373 : Int)/10^30,(-4062282907147723237343238475 : Int)/10^30)
theorem v4447_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 72 92 5) 1) 14) v4447_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4447 : Material (72 : Basis) (92 : Basis) where
  plus := ![v4447_pa,v4447_pb,v4447_pg]
  minus := ![(Primitive.Addresses.material4447 1).one,v4447_mb,v4447_mg]
  upper := v4447_upper
  lower := (Primitive.Addresses.material4447 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4447_pa_checked.trans (by decide +kernel)
    · exact v4447_pb_checked.trans (by decide +kernel)
    · exact v4447_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 72 92 Primitive.Addresses.material4447
    · exact v4447_mb_checked.trans (by decide +kernel)
    · exact v4447_mg_checked.trans (by decide +kernel)
  upper_error := v4447_upper_checked
  lower_error := reuse_lower_error 72 92 Primitive.Addresses.material4447

def v4448_pa : Scalar.QComplex := ((999997181328394798660612291555 : Int)/10^30,(-2374307323303590538609787745 : Int)/10^30)
theorem v4448_pa_checked : Scalar.distance (sourceCoefficient 72 93 1 0) v4448_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4448_pb : Scalar.QComplex := ((-1024460210636992452119870 : Int)/10^30,(-431476293302530470595285080 : Int)/10^30)
theorem v4448_pb_checked : Scalar.distance (sourceCoefficient 72 93 1 1) v4448_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4448_pg : Scalar.QComplex := ((-93086166275895928312351 : Int)/10^30,(221015789258044903149 : Int)/10^30)
theorem v4448_pg_checked : Scalar.distance (sourceCoefficient 72 93 1 2) v4448_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4448_mb : Scalar.QComplex := ((-1396804437332855125057764 : Int)/10^30,(-431475248581165228665344661 : Int)/10^30)
theorem v4448_mb_checked : Scalar.distance (sourceCoefficient 72 93 3 1) v4448_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4448_mg : Scalar.QComplex := ((-93085940888990027772215 : Int)/10^30,(301344876014565646557 : Int)/10^30)
theorem v4448_mg_checked : Scalar.distance (sourceCoefficient 72 93 3 2) v4448_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4448_upper : Scalar.QComplex := ((999991594111016586402452687750 : Int)/10^30,(-4100208202988915735011512340 : Int)/10^30)
theorem v4448_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 72 93 5) 1) 14) v4448_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4448 : Material (72 : Basis) (93 : Basis) where
  plus := ![v4448_pa,v4448_pb,v4448_pg]
  minus := ![(Primitive.Addresses.material4448 1).one,v4448_mb,v4448_mg]
  upper := v4448_upper
  lower := (Primitive.Addresses.material4448 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4448_pa_checked.trans (by decide +kernel)
    · exact v4448_pb_checked.trans (by decide +kernel)
    · exact v4448_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 72 93 Primitive.Addresses.material4448
    · exact v4448_mb_checked.trans (by decide +kernel)
    · exact v4448_mg_checked.trans (by decide +kernel)
  upper_error := v4448_upper_checked
  lower_error := reuse_lower_error 72 93 Primitive.Addresses.material4448

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
