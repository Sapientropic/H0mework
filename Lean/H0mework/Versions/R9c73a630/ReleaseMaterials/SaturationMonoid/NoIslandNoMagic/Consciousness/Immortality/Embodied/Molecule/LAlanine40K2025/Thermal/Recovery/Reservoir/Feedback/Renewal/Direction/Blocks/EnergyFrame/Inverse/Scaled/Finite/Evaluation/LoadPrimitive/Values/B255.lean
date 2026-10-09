import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B170

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4081_pa : Scalar.QComplex := ((999997913021721954372300686809 : Int)/10^30,(-2043025256968920187297541957 : Int)/10^30)
theorem v4081_pa_checked : Scalar.distance (sourceCoefficient 60 92 1 0) v4081_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4081_pb : Scalar.QComplex := ((-881519410107768210351642 : Int)/10^30,(-431476589625596513824745371 : Int)/10^30)
theorem v4081_pb_checked : Scalar.distance (sourceCoefficient 60 92 1 1) v4081_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4081_pg : Scalar.QComplex := ((-93086232295442705041149 : Int)/10^30,(190177920552854587425 : Int)/10^30)
theorem v4081_pg_checked : Scalar.distance (sourceCoefficient 60 92 1 2) v4081_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4081_mb : Scalar.QComplex := ((-1253863945740483737462054 : Int)/10^30,(-431475668255593979322282455 : Int)/10^30)
theorem v4081_mb_checked : Scalar.distance (sourceCoefficient 60 92 3 1) v4081_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4081_mg : Scalar.QComplex := ((-93086033520204028937139 : Int)/10^30,(270507075763618668308 : Int)/10^30)
theorem v4081_mg_checked : Scalar.distance (sourceCoefficient 60 92 3 2) v4081_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4081_upper : Scalar.QComplex := ((999992897566046790203643600170 : Int)/10^30,(-3768927892896272034681397032 : Int)/10^30)
theorem v4081_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 92 5) 1) 14) v4081_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4081 : Material (60 : Basis) (92 : Basis) where
  plus := ![v4081_pa,v4081_pb,v4081_pg]
  minus := ![(Primitive.Addresses.material4081 1).one,v4081_mb,v4081_mg]
  upper := v4081_upper
  lower := (Primitive.Addresses.material4081 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4081_pa_checked.trans (by decide +kernel)
    · exact v4081_pb_checked.trans (by decide +kernel)
    · exact v4081_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 92 Primitive.Addresses.material4081
    · exact v4081_mb_checked.trans (by decide +kernel)
    · exact v4081_mg_checked.trans (by decide +kernel)
  upper_error := v4081_upper_checked
  lower_error := reuse_lower_error 60 92 Primitive.Addresses.material4081

def v4082_pa : Scalar.QComplex := ((999997834819564873444036989352 : Int)/10^30,(-2080950788040600269879479907 : Int)/10^30)
theorem v4082_pa_checked : Scalar.distance (sourceCoefficient 60 93 1 0) v4082_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4082_pb : Scalar.QComplex := ((-897883415410920256828392 : Int)/10^30,(-431476552204654116033660775 : Int)/10^30)
theorem v4082_pb_checked : Scalar.distance (sourceCoefficient 60 93 1 1) v4082_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4082_pg : Scalar.QComplex := ((-93086224619088843559938 : Int)/10^30,(193708271890177673478 : Int)/10^30)
theorem v4082_pg_checked : Scalar.distance (sourceCoefficient 60 93 1 2) v4082_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4082_mb : Scalar.QComplex := ((-1270227912657980824975085 : Int)/10^30,(-431475616713265945877909781 : Int)/10^30)
theorem v4082_mb_checked : Scalar.distance (sourceCoefficient 60 93 3 1) v4082_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4082_mg : Scalar.QComplex := ((-93086022797318822725308 : Int)/10^30,(274037419162082954134 : Int)/10^30)
theorem v4082_mg_checked : Scalar.distance (sourceCoefficient 60 93 3 2) v4082_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4082_upper : Scalar.QComplex := ((999992753907980129784766596719 : Int)/10^30,(-3806853232512499954414873606 : Int)/10^30)
theorem v4082_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 93 5) 1) 14) v4082_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4082 : Material (60 : Basis) (93 : Basis) where
  plus := ![v4082_pa,v4082_pb,v4082_pg]
  minus := ![(Primitive.Addresses.material4082 1).one,v4082_mb,v4082_mg]
  upper := v4082_upper
  lower := (Primitive.Addresses.material4082 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4082_pa_checked.trans (by decide +kernel)
    · exact v4082_pb_checked.trans (by decide +kernel)
    · exact v4082_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 93 Primitive.Addresses.material4082
    · exact v4082_mb_checked.trans (by decide +kernel)
    · exact v4082_mg_checked.trans (by decide +kernel)
  upper_error := v4082_upper_checked
  lower_error := reuse_lower_error 60 93 Primitive.Addresses.material4082

def v4083_pa : Scalar.QComplex := ((999997740592518174451069073909 : Int)/10^30,(-2125749246437342367612603092 : Int)/10^30)
theorem v4083_pa_checked : Scalar.distance (sourceCoefficient 60 94 1 0) v4083_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4083_pb : Scalar.QComplex := ((-917212931832827984423651 : Int)/10^30,(-431476506936211053498926062 : Int)/10^30)
theorem v4083_pb_checked : Scalar.distance (sourceCoefficient 60 94 1 1) v4083_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4083_pg : Scalar.QComplex := ((-93086215350380025895779 : Int)/10^30,(197878399222710207129 : Int)/10^30)
theorem v4083_pg_checked : Scalar.distance (sourceCoefficient 60 94 1 2) v4083_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4083_mb : Scalar.QComplex := ((-1289557382817998638176335 : Int)/10^30,(-431475554764337635849626947 : Int)/10^30)
theorem v4083_mb_checked : Scalar.distance (sourceCoefficient 60 94 3 1) v4083_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4083_mg : Scalar.QComplex := ((-93086009929981383812483 : Int)/10^30,(278207536943408235154 : Int)/10^30)
theorem v4083_mg_checked : Scalar.distance (sourceCoefficient 60 94 3 2) v4083_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4083_upper : Scalar.QComplex := ((999992582362998662531177042988 : Int)/10^30,(-3851651461559866275226832725 : Int)/10^30)
theorem v4083_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 94 5) 1) 14) v4083_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4083 : Material (60 : Basis) (94 : Basis) where
  plus := ![v4083_pa,v4083_pb,v4083_pg]
  minus := ![(Primitive.Addresses.material4083 1).one,v4083_mb,v4083_mg]
  upper := v4083_upper
  lower := (Primitive.Addresses.material4083 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4083_pa_checked.trans (by decide +kernel)
    · exact v4083_pb_checked.trans (by decide +kernel)
    · exact v4083_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 94 Primitive.Addresses.material4083
    · exact v4083_mb_checked.trans (by decide +kernel)
    · exact v4083_mg_checked.trans (by decide +kernel)
  upper_error := v4083_upper_checked
  lower_error := reuse_lower_error 60 94 Primitive.Addresses.material4083

def v4084_pa : Scalar.QComplex := ((999997645496519367268017714291 : Int)/10^30,(-2170023367979898886720492244 : Int)/10^30)
theorem v4084_pa_checked : Scalar.distance (sourceCoefficient 60 95 1 0) v4084_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4084_pb : Scalar.QComplex := ((-936316207800213060630503 : Int)/10^30,(-431476461063213757709990459 : Int)/10^30)
theorem v4084_pb_checked : Scalar.distance (sourceCoefficient 60 95 1 1) v4084_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4084_pg : Scalar.QComplex := ((-93086205976014488639348 : Int)/10^30,(201999717813580230387 : Int)/10^30)
theorem v4084_pg_checked : Scalar.distance (sourceCoefficient 60 95 1 2) v4084_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4084_mb : Scalar.QComplex := ((-1308660612086030385721060 : Int)/10^30,(-431475492406090640431541921 : Int)/10^30)
theorem v4084_mb_checked : Scalar.distance (sourceCoefficient 60 95 3 1) v4084_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4084_mg : Scalar.QComplex := ((-93085996999107010438835 : Int)/10^30,(282328845910067740565 : Int)/10^30)
theorem v4084_mg_checked : Scalar.distance (sourceCoefficient 60 95 3 2) v4084_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4084_upper : Scalar.QComplex := ((999992410854024224146068567915 : Int)/10^30,(-3895925353034252660772796127 : Int)/10^30)
theorem v4084_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 95 5) 1) 14) v4084_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4084 : Material (60 : Basis) (95 : Basis) where
  plus := ![v4084_pa,v4084_pb,v4084_pg]
  minus := ![(Primitive.Addresses.material4084 1).one,v4084_mb,v4084_mg]
  upper := v4084_upper
  lower := (Primitive.Addresses.material4084 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4084_pa_checked.trans (by decide +kernel)
    · exact v4084_pb_checked.trans (by decide +kernel)
    · exact v4084_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 95 Primitive.Addresses.material4084
    · exact v4084_mb_checked.trans (by decide +kernel)
    · exact v4084_mg_checked.trans (by decide +kernel)
  upper_error := v4084_upper_checked
  lower_error := reuse_lower_error 60 95 Primitive.Addresses.material4084

def v4085_pa : Scalar.QComplex := ((999997599126852372775127122110 : Int)/10^30,(-2191287414070226148867144816 : Int)/10^30)
theorem v4085_pa_checked : Scalar.distance (sourceCoefficient 60 96 1 0) v4085_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4085_pb : Scalar.QComplex := ((-945491159442935646003069 : Int)/10^30,(-431476438630381642814429204 : Int)/10^30)
theorem v4085_pb_checked : Scalar.distance (sourceCoefficient 60 96 1 1) v4085_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4085_pg : Scalar.QComplex := ((-93086201398005297458899 : Int)/10^30,(203979111275026235540 : Int)/10^30)
theorem v4085_pg_checked : Scalar.distance (sourceCoefficient 60 96 1 2) v4085_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4085_mb : Scalar.QComplex := ((-1317835540953975380601407 : Int)/10^30,(-431475462055696835117391334 : Int)/10^30)
theorem v4085_mb_checked : Scalar.distance (sourceCoefficient 60 96 3 1) v4085_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4085_mg : Scalar.QComplex := ((-93085990712972115204685 : Int)/10^30,(284308234683879351162 : Int)/10^30)
theorem v4085_mg_checked : Scalar.distance (sourceCoefficient 60 96 3 2) v4085_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4085_upper : Scalar.QComplex := ((999992327784611799112679134568 : Int)/10^30,(-3917189287424442512529849440 : Int)/10^30)
theorem v4085_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 96 5) 1) 14) v4085_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4085 : Material (60 : Basis) (96 : Basis) where
  plus := ![v4085_pa,v4085_pb,v4085_pg]
  minus := ![(Primitive.Addresses.material4085 1).one,v4085_mb,v4085_mg]
  upper := v4085_upper
  lower := (Primitive.Addresses.material4085 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4085_pa_checked.trans (by decide +kernel)
    · exact v4085_pb_checked.trans (by decide +kernel)
    · exact v4085_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 96 Primitive.Addresses.material4085
    · exact v4085_mb_checked.trans (by decide +kernel)
    · exact v4085_mg_checked.trans (by decide +kernel)
  upper_error := v4085_upper_checked
  lower_error := reuse_lower_error 60 96 Primitive.Addresses.material4085

def v4086_pa : Scalar.QComplex := ((999997436131044374892710499841 : Int)/10^30,(-2264449455789683321767574299 : Int)/10^30)
theorem v4086_pa_checked : Scalar.distance (sourceCoefficient 60 97 1 0) v4086_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4086_pb : Scalar.QComplex := ((-977058912415727066536477 : Int)/10^30,(-431476359459736327928240125 : Int)/10^30)
theorem v4086_pb_checked : Scalar.distance (sourceCoefficient 60 97 1 1) v4086_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4086_pg : Scalar.QComplex := ((-93086185271567514895584 : Int)/10^30,(210789502016399085619 : Int)/10^30)
theorem v4086_pg_checked : Scalar.distance (sourceCoefficient 60 97 1 2) v4086_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4086_mb : Scalar.QComplex := ((-1349403213851948458534713 : Int)/10^30,(-431475355643531942377460731 : Int)/10^30)
theorem v4086_mb_checked : Scalar.distance (sourceCoefficient 60 97 3 1) v4086_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4086_mg : Scalar.QComplex := ((-93085968709479856059091 : Int)/10^30,(291118608973042979439 : Int)/10^30)
theorem v4086_mg_checked : Scalar.distance (sourceCoefficient 60 97 3 2) v4086_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4086_upper : Scalar.QComplex := ((999992038517999765134123359703 : Int)/10^30,(-3990350938861655021277886165 : Int)/10^30)
theorem v4086_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 60 97 5) 1) 14) v4086_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4086 : Material (60 : Basis) (97 : Basis) where
  plus := ![v4086_pa,v4086_pb,v4086_pg]
  minus := ![(Primitive.Addresses.material4086 1).one,v4086_mb,v4086_mg]
  upper := v4086_upper
  lower := (Primitive.Addresses.material4086 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4086_pa_checked.trans (by decide +kernel)
    · exact v4086_pb_checked.trans (by decide +kernel)
    · exact v4086_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 60 97 Primitive.Addresses.material4086
    · exact v4086_mb_checked.trans (by decide +kernel)
    · exact v4086_mg_checked.trans (by decide +kernel)
  upper_error := v4086_upper_checked
  lower_error := reuse_lower_error 60 97 Primitive.Addresses.material4086

def v4087_pa : Scalar.QComplex := ((999999008978626244055400388278 : Int)/10^30,(-1407850050747069426017952724 : Int)/10^30)
theorem v4087_pa_checked : Scalar.distance (sourceCoefficient 61 62 1 0) v4087_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4087_pb : Scalar.QComplex := ((-607455649829650785305922 : Int)/10^30,(-431477093391995014536607764 : Int)/10^30)
theorem v4087_pb_checked : Scalar.distance (sourceCoefficient 61 62 1 1) v4087_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4087_pg : Scalar.QComplex := ((-93086337645772194850780 : Int)/10^30,(131051735053529729494 : Int)/10^30)
theorem v4087_pg_checked : Scalar.distance (sourceCoefficient 61 62 1 2) v4087_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4087_mb : Scalar.QComplex := ((-979800722236542706341721 : Int)/10^30,(-431476408526486651240697264 : Int)/10^30)
theorem v4087_mb_checked : Scalar.distance (sourceCoefficient 61 62 3 1) v4087_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4087_mg : Scalar.QComplex := ((-93086189893729433379964 : Int)/10^30,(211381003192264418944 : Int)/10^30)
theorem v4087_mg_checked : Scalar.distance (sourceCoefficient 61 62 3 2) v4087_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4087_upper : Scalar.QComplex := ((999995089776102075147310416233 : Int)/10^30,(-3133755524215470390150789171 : Int)/10^30)
theorem v4087_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 62 5) 1) 14) v4087_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4087 : Material (61 : Basis) (62 : Basis) where
  plus := ![v4087_pa,v4087_pb,v4087_pg]
  minus := ![(Primitive.Addresses.material4087 1).one,v4087_mb,v4087_mg]
  upper := v4087_upper
  lower := (Primitive.Addresses.material4087 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4087_pa_checked.trans (by decide +kernel)
    · exact v4087_pb_checked.trans (by decide +kernel)
    · exact v4087_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 62 Primitive.Addresses.material4087
    · exact v4087_mb_checked.trans (by decide +kernel)
    · exact v4087_mg_checked.trans (by decide +kernel)
  upper_error := v4087_upper_checked
  lower_error := reuse_lower_error 61 62 Primitive.Addresses.material4087

def v4088_pa : Scalar.QComplex := ((999998973763339498896187693431 : Int)/10^30,(-1432645199566356090107754736 : Int)/10^30)
theorem v4088_pa_checked : Scalar.distance (sourceCoefficient 61 63 1 0) v4088_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4088_pb : Scalar.QComplex := ((-618154199068073897251291 : Int)/10^30,(-431477078122818111618045036 : Int)/10^30)
theorem v4088_pb_checked : Scalar.distance (sourceCoefficient 61 63 1 1) v4088_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4088_pg : Scalar.QComplex := ((-93086334359662808364737 : Int)/10^30,(133359826924343101876 : Int)/10^30)
theorem v4088_pg_checked : Scalar.distance (sourceCoefficient 61 63 1 2) v4088_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4088_mb : Scalar.QComplex := ((-990499254314795019947886 : Int)/10^30,(-431476384024949285746165646 : Int)/10^30)
theorem v4088_mb_checked : Scalar.distance (sourceCoefficient 61 63 3 1) v4088_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4088_mg : Scalar.QComplex := ((-93086184615841938549648 : Int)/10^30,(213689091367905303149 : Int)/10^30)
theorem v4088_mg_checked : Scalar.distance (sourceCoefficient 61 63 3 2) v4088_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4088_upper : Scalar.QComplex := ((999995011766690315261794472499 : Int)/10^30,(-3158550575326905314408461691 : Int)/10^30)
theorem v4088_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 63 5) 1) 14) v4088_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4088 : Material (61 : Basis) (63 : Basis) where
  plus := ![v4088_pa,v4088_pb,v4088_pg]
  minus := ![(Primitive.Addresses.material4088 1).one,v4088_mb,v4088_mg]
  upper := v4088_upper
  lower := (Primitive.Addresses.material4088 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4088_pa_checked.trans (by decide +kernel)
    · exact v4088_pb_checked.trans (by decide +kernel)
    · exact v4088_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 63 Primitive.Addresses.material4088
    · exact v4088_mb_checked.trans (by decide +kernel)
    · exact v4088_mg_checked.trans (by decide +kernel)
  upper_error := v4088_upper_checked
  lower_error := reuse_lower_error 61 63 Primitive.Addresses.material4088

def v4089_pa : Scalar.QComplex := ((999998922366403212522676095078 : Int)/10^30,(-1468082433748454645235306647 : Int)/10^30)
theorem v4089_pa_checked : Scalar.distance (sourceCoefficient 61 64 1 0) v4089_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4089_pb : Scalar.QComplex := ((-633444568639446407442520 : Int)/10^30,(-431477055686120680106997909 : Int)/10^30)
theorem v4089_pb_checked : Scalar.distance (sourceCoefficient 61 64 1 1) v4089_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4089_pg : Scalar.QComplex := ((-93086329547251395909790 : Int)/10^30,(136658552498286974027 : Int)/10^30)
theorem v4089_pg_checked : Scalar.distance (sourceCoefficient 61 64 1 2) v4089_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4089_mb : Scalar.QComplex := ((-1005789598831004762252417 : Int)/10^30,(-431476348393359921030009139 : Int)/10^30)
theorem v4089_mb_checked : Scalar.distance (sourceCoefficient 61 64 3 1) v4089_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4089_mg : Scalar.QComplex := ((-93086176956780716746553 : Int)/10^30,(216987811560688578929 : Int)/10^30)
theorem v4089_mg_checked : Scalar.distance (sourceCoefficient 61 64 3 2) v4089_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4089_upper : Scalar.QComplex := ((999994899208379221057309057776 : Int)/10^30,(-3193987668022956968600734678 : Int)/10^30)
theorem v4089_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 64 5) 1) 14) v4089_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4089 : Material (61 : Basis) (64 : Basis) where
  plus := ![v4089_pa,v4089_pb,v4089_pg]
  minus := ![(Primitive.Addresses.material4089 1).one,v4089_mb,v4089_mg]
  upper := v4089_upper
  lower := (Primitive.Addresses.material4089 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4089_pa_checked.trans (by decide +kernel)
    · exact v4089_pb_checked.trans (by decide +kernel)
    · exact v4089_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 64 Primitive.Addresses.material4089
    · exact v4089_mb_checked.trans (by decide +kernel)
    · exact v4089_mg_checked.trans (by decide +kernel)
  upper_error := v4089_upper_checked
  lower_error := reuse_lower_error 61 64 Primitive.Addresses.material4089

def v4090_pa : Scalar.QComplex := ((999998868917643712542482419461 : Int)/10^30,(-1504049012907364774609745005 : Int)/10^30)
theorem v4090_pa_checked : Scalar.distance (sourceCoefficient 61 65 1 0) v4090_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4090_pb : Scalar.QComplex := ((-648963338366801157406812 : Int)/10^30,(-431477032175539365509411022 : Int)/10^30)
theorem v4090_pb_checked : Scalar.distance (sourceCoefficient 61 65 1 1) v4090_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4090_pg : Scalar.QComplex := ((-93086324523502340446355 : Int)/10^30,(140006552873690037856 : Int)/10^30)
theorem v4090_pg_checked : Scalar.distance (sourceCoefficient 61 65 1 2) v4090_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4090_mb : Scalar.QComplex := ((-1021308342491439502686010 : Int)/10^30,(-431476311490788025231851454 : Int)/10^30)
theorem v4090_mb_checked : Scalar.distance (sourceCoefficient 61 65 3 1) v4090_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4090_mg : Scalar.QComplex := ((-93086169043859996221025 : Int)/10^30,(220335806354208918213 : Int)/10^30)
theorem v4090_mg_checked : Scalar.distance (sourceCoefficient 61 65 3 2) v4090_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4090_upper : Scalar.QComplex := ((999994783684646561020187618694 : Int)/10^30,(-3229954101366162308570783313 : Int)/10^30)
theorem v4090_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 65 5) 1) 14) v4090_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4090 : Material (61 : Basis) (65 : Basis) where
  plus := ![v4090_pa,v4090_pb,v4090_pg]
  minus := ![(Primitive.Addresses.material4090 1).one,v4090_mb,v4090_mg]
  upper := v4090_upper
  lower := (Primitive.Addresses.material4090 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4090_pa_checked.trans (by decide +kernel)
    · exact v4090_pb_checked.trans (by decide +kernel)
    · exact v4090_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 65 Primitive.Addresses.material4090
    · exact v4090_mb_checked.trans (by decide +kernel)
    · exact v4090_mg_checked.trans (by decide +kernel)
  upper_error := v4090_upper_checked
  lower_error := reuse_lower_error 61 65 Primitive.Addresses.material4090

def v4091_pa : Scalar.QComplex := ((999998842310420577087493145823 : Int)/10^30,(-1521636559300762433316985743 : Int)/10^30)
theorem v4091_pa_checked : Scalar.distance (sourceCoefficient 61 66 1 0) v4091_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4091_pb : Scalar.QComplex := ((-656551968834349374674591 : Int)/10^30,(-431477020408001794713207913 : Int)/10^30)
theorem v4091_pb_checked : Scalar.distance (sourceCoefficient 61 66 1 1) v4091_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4091_pg : Scalar.QComplex := ((-93086322015759591233155 : Int)/10^30,(141643714729475769959 : Int)/10^30)
theorem v4091_pg_checked : Scalar.distance (sourceCoefficient 61 66 1 2) v4091_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4091_mb : Scalar.QComplex := ((-1028896959978538845960990 : Int)/10^30,(-431476293174608521762394506 : Int)/10^30)
theorem v4091_mb_checked : Scalar.distance (sourceCoefficient 61 66 3 1) v4091_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4091_mg : Scalar.QComplex := ((-93086165123321234244786 : Int)/10^30,(221972965436335421384 : Int)/10^30)
theorem v4091_mg_checked : Scalar.distance (sourceCoefficient 61 66 3 2) v4091_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4091_upper : Scalar.QComplex := ((999994726722953508639410340385 : Int)/10^30,(-3247541575643322249270698436 : Int)/10^30)
theorem v4091_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 66 5) 1) 14) v4091_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4091 : Material (61 : Basis) (66 : Basis) where
  plus := ![v4091_pa,v4091_pb,v4091_pg]
  minus := ![(Primitive.Addresses.material4091 1).one,v4091_mb,v4091_mg]
  upper := v4091_upper
  lower := (Primitive.Addresses.material4091 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4091_pa_checked.trans (by decide +kernel)
    · exact v4091_pb_checked.trans (by decide +kernel)
    · exact v4091_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 66 Primitive.Addresses.material4091
    · exact v4091_mb_checked.trans (by decide +kernel)
    · exact v4091_mg_checked.trans (by decide +kernel)
  upper_error := v4091_upper_checked
  lower_error := reuse_lower_error 61 66 Primitive.Addresses.material4091

def v4092_pa : Scalar.QComplex := ((999998796960407697390826192050 : Int)/10^30,(-1551153679459568474122994510 : Int)/10^30)
theorem v4092_pa_checked : Scalar.distance (sourceCoefficient 61 67 1 0) v4092_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4092_pb : Scalar.QComplex := ((-669287941733247675200164 : Int)/10^30,(-431477000258632589526553244 : Int)/10^30)
theorem v4092_pb_checked : Scalar.distance (sourceCoefficient 61 67 1 1) v4092_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4092_pg : Scalar.QComplex := ((-93086317731524124644342 : Int)/10^30,(144391357965116535595 : Int)/10^30)
theorem v4092_pg_checked : Scalar.distance (sourceCoefficient 61 67 1 2) v4092_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4092_mb : Scalar.QComplex := ((-1041632910747254243335926 : Int)/10^30,(-431476262034675814283609623 : Int)/10^30)
theorem v4092_mb_checked : Scalar.distance (sourceCoefficient 61 67 3 1) v4092_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4092_mg : Scalar.QComplex := ((-93086158467994999772200 : Int)/10^30,(224720603951800784028 : Int)/10^30)
theorem v4092_mg_checked : Scalar.distance (sourceCoefficient 61 67 3 2) v4092_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4092_upper : Scalar.QComplex := ((999994630429136550583712737429 : Int)/10^30,(-3277058573569837028709473542 : Int)/10^30)
theorem v4092_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 67 5) 1) 14) v4092_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4092 : Material (61 : Basis) (67 : Basis) where
  plus := ![v4092_pa,v4092_pb,v4092_pg]
  minus := ![(Primitive.Addresses.material4092 1).one,v4092_mb,v4092_mg]
  upper := v4092_upper
  lower := (Primitive.Addresses.material4092 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4092_pa_checked.trans (by decide +kernel)
    · exact v4092_pb_checked.trans (by decide +kernel)
    · exact v4092_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 67 Primitive.Addresses.material4092
    · exact v4092_mb_checked.trans (by decide +kernel)
    · exact v4092_mg_checked.trans (by decide +kernel)
  upper_error := v4092_upper_checked
  lower_error := reuse_lower_error 61 67 Primitive.Addresses.material4092

def v4093_pa : Scalar.QComplex := ((999998719500569224452114433945 : Int)/10^30,(-1600311601492754146255530174 : Int)/10^30)
theorem v4093_pa_checked : Scalar.distance (sourceCoefficient 61 68 1 0) v4093_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4093_pb : Scalar.QComplex := ((-690498477992356767553935 : Int)/10^30,(-431476965589301307046534549 : Int)/10^30)
theorem v4093_pb_checked : Scalar.distance (sourceCoefficient 61 68 1 1) v4093_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4093_pg : Scalar.QComplex := ((-93086310386534760644097 : Int)/10^30,(148967293204261189282 : Int)/10^30)
theorem v4093_pg_checked : Scalar.distance (sourceCoefficient 61 68 1 2) v4093_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4093_mb : Scalar.QComplex := ((-1062843409190639868965527 : Int)/10^30,(-431476209061619936260133954 : Int)/10^30)
theorem v4093_mb_checked : Scalar.distance (sourceCoefficient 61 68 3 1) v4093_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4093_mg : Scalar.QComplex := ((-93086147174182351738000 : Int)/10^30,(229296531148720602518 : Int)/10^30)
theorem v4093_mg_checked : Scalar.distance (sourceCoefficient 61 68 3 2) v4093_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4093_upper : Scalar.QComplex := ((999994468127299587547451584304 : Int)/10^30,(-3326216288699418224931472229 : Int)/10^30)
theorem v4093_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 68 5) 1) 14) v4093_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4093 : Material (61 : Basis) (68 : Basis) where
  plus := ![v4093_pa,v4093_pb,v4093_pg]
  minus := ![(Primitive.Addresses.material4093 1).one,v4093_mb,v4093_mg]
  upper := v4093_upper
  lower := (Primitive.Addresses.material4093 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4093_pa_checked.trans (by decide +kernel)
    · exact v4093_pb_checked.trans (by decide +kernel)
    · exact v4093_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 68 Primitive.Addresses.material4093
    · exact v4093_mb_checked.trans (by decide +kernel)
    · exact v4093_mg_checked.trans (by decide +kernel)
  upper_error := v4093_upper_checked
  lower_error := reuse_lower_error 61 68 Primitive.Addresses.material4093

def v4094_pa : Scalar.QComplex := ((999998684643162476435918721445 : Int)/10^30,(-1621946961180765042147600919 : Int)/10^30)
theorem v4094_pa_checked : Scalar.distance (sourceCoefficient 61 69 1 0) v4094_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4094_pb : Scalar.QComplex := ((-699833648224723761909994 : Int)/10^30,(-431476949890073188050643709 : Int)/10^30)
theorem v4094_pb_checked : Scalar.distance (sourceCoefficient 61 69 1 1) v4094_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4094_pg : Scalar.QComplex := ((-93086307070692899958107 : Int)/10^30,(150981251475071377072 : Int)/10^30)
theorem v4094_pg_checked : Scalar.distance (sourceCoefficient 61 69 1 2) v4094_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4094_mb : Scalar.QComplex := ((-1072178562399369547748838 : Int)/10^30,(-431476185306566192731428162 : Int)/10^30)
theorem v4094_mb_checked : Scalar.distance (sourceCoefficient 61 69 3 1) v4094_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4094_mg : Scalar.QComplex := ((-93086142120386443295662 : Int)/10^30,(231310485808219897847 : Int)/10^30)
theorem v4094_mg_checked : Scalar.distance (sourceCoefficient 61 69 3 2) v4094_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4094_upper : Scalar.QComplex := ((999994395929276678535939828943 : Int)/10^30,(-3347851556003380525570817393 : Int)/10^30)
theorem v4094_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 69 5) 1) 14) v4094_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4094 : Material (61 : Basis) (69 : Basis) where
  plus := ![v4094_pa,v4094_pb,v4094_pg]
  minus := ![(Primitive.Addresses.material4094 1).one,v4094_mb,v4094_mg]
  upper := v4094_upper
  lower := (Primitive.Addresses.material4094 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4094_pa_checked.trans (by decide +kernel)
    · exact v4094_pb_checked.trans (by decide +kernel)
    · exact v4094_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 69 Primitive.Addresses.material4094
    · exact v4094_mb_checked.trans (by decide +kernel)
    · exact v4094_mg_checked.trans (by decide +kernel)
  upper_error := v4094_upper_checked
  lower_error := reuse_lower_error 61 69 Primitive.Addresses.material4094

def v4095_pa : Scalar.QComplex := ((999998661458393907839047939188 : Int)/10^30,(-1636178908460407536352337074 : Int)/10^30)
theorem v4095_pa_checked : Scalar.distance (sourceCoefficient 61 70 1 0) v4095_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4095_pb : Scalar.QComplex := ((-705974412735852825423793 : Int)/10^30,(-431476939416134624402452744 : Int)/10^30)
theorem v4095_pb_checked : Scalar.distance (sourceCoefficient 61 70 1 1) v4095_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4095_pg : Scalar.QComplex := ((-93086304861781919097461 : Int)/10^30,(152306052549351264578 : Int)/10^30)
theorem v4095_pg_checked : Scalar.distance (sourceCoefficient 61 70 1 2) v4095_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4095_mb : Scalar.QComplex := ((-1078319315585474085220021 : Int)/10^30,(-431476169533428325671694187 : Int)/10^30)
theorem v4095_mb_checked : Scalar.distance (sourceCoefficient 61 70 3 1) v4095_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4095_mg : Scalar.QComplex := ((-93086138768232624635433 : Int)/10^30,(232635284483025108174 : Int)/10^30)
theorem v4095_mg_checked : Scalar.distance (sourceCoefficient 61 70 3 2) v4095_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4095_upper : Scalar.QComplex := ((999994348181492748437027109547 : Int)/10^30,(-3362083442071402105089429151 : Int)/10^30)
theorem v4095_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 70 5) 1) 14) v4095_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4095 : Material (61 : Basis) (70 : Basis) where
  plus := ![v4095_pa,v4095_pb,v4095_pg]
  minus := ![(Primitive.Addresses.material4095 1).one,v4095_mb,v4095_mg]
  upper := v4095_upper
  lower := (Primitive.Addresses.material4095 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4095_pa_checked.trans (by decide +kernel)
    · exact v4095_pb_checked.trans (by decide +kernel)
    · exact v4095_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 70 Primitive.Addresses.material4095
    · exact v4095_mb_checked.trans (by decide +kernel)
    · exact v4095_mg_checked.trans (by decide +kernel)
  upper_error := v4095_upper_checked
  lower_error := reuse_lower_error 61 70 Primitive.Addresses.material4095

def v4096_pa : Scalar.QComplex := ((999998621415929843318663337790 : Int)/10^30,(-1660471691965666779810887319 : Int)/10^30)
theorem v4096_pa_checked : Scalar.distance (sourceCoefficient 61 71 1 0) v4096_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4096_pb : Scalar.QComplex := ((-716456201198383805831406 : Int)/10^30,(-431476921268761901249989565 : Int)/10^30)
theorem v4096_pb_checked : Scalar.distance (sourceCoefficient 61 71 1 1) v4096_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4096_pg : Scalar.QComplex := ((-93086301040530967828874 : Int)/10^30,(154567380871724899859 : Int)/10^30)
theorem v4096_pg_checked : Scalar.distance (sourceCoefficient 61 71 1 2) v4096_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4096_mb : Scalar.QComplex := ((-1088801084484790846875745 : Int)/10^30,(-431476142340750998679072002 : Int)/10^30)
theorem v4096_mb_checked : Scalar.distance (sourceCoefficient 61 71 3 1) v4096_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4096_mg : Scalar.QComplex := ((-93086132995558600431690 : Int)/10^30,(234896608665835393035 : Int)/10^30)
theorem v4096_mg_checked : Scalar.distance (sourceCoefficient 61 71 3 2) v4096_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4096_upper : Scalar.QComplex := ((999994266211947816489962120193 : Int)/10^30,(-3386376120285753596872743336 : Int)/10^30)
theorem v4096_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 61 71 5) 1) 14) v4096_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4096 : Material (61 : Basis) (71 : Basis) where
  plus := ![v4096_pa,v4096_pb,v4096_pg]
  minus := ![(Primitive.Addresses.material4096 1).one,v4096_mb,v4096_mg]
  upper := v4096_upper
  lower := (Primitive.Addresses.material4096 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4096_pa_checked.trans (by decide +kernel)
    · exact v4096_pb_checked.trans (by decide +kernel)
    · exact v4096_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 61 71 Primitive.Addresses.material4096
    · exact v4096_mb_checked.trans (by decide +kernel)
    · exact v4096_mg_checked.trans (by decide +kernel)
  upper_error := v4096_upper_checked
  lower_error := reuse_lower_error 61 71 Primitive.Addresses.material4096

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
