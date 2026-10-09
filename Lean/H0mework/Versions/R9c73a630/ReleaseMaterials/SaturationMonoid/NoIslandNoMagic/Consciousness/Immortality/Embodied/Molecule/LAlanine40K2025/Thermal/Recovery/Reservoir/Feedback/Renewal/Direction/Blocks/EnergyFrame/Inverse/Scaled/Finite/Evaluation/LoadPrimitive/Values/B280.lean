import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B186
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B187

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4481_pa : Scalar.QComplex := ((999997862726121767998747855701 : Int)/10^30,(-2067496841236854690887816039 : Int)/10^30)
theorem v4481_pa_checked : Scalar.distance (sourceCoefficient 74 79 1 0) v4481_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4481_pb : Scalar.QComplex := ((-892078411315921736712811 : Int)/10^30,(-431476598613017489055770220 : Int)/10^30)
theorem v4481_pb_checked : Scalar.distance (sourceCoefficient 74 79 1 1) v4481_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4481_pg : Scalar.QComplex := ((-93086230923991343411103 : Int)/10^30,(192455899728963726417 : Int)/10^30)
theorem v4481_pg_checked : Scalar.distance (sourceCoefficient 74 79 1 2) v4481_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4481_mb : Scalar.QComplex := ((-1264422950772778067042733 : Int)/10^30,(-431475668131069125250046644 : Int)/10^30)
theorem v4481_mb_checked : Scalar.distance (sourceCoefficient 74 79 3 1) v4481_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4481_mg : Scalar.QComplex := ((-93086030182959745352463 : Int)/10^30,(272785052908031294032 : Int)/10^30)
theorem v4481_mg_checked : Scalar.distance (sourceCoefficient 74 79 3 2) v4481_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4481_upper : Scalar.QComplex := ((999992805034787111546227832316 : Int)/10^30,(-3793399353911013264929044735 : Int)/10^30)
theorem v4481_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 74 79 5) 1) 14) v4481_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4481 : Material (74 : Basis) (79 : Basis) where
  plus := ![v4481_pa,v4481_pb,v4481_pg]
  minus := ![(Primitive.Addresses.material4481 1).one,v4481_mb,v4481_mg]
  upper := v4481_upper
  lower := (Primitive.Addresses.material4481 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4481_pa_checked.trans (by decide +kernel)
    · exact v4481_pb_checked.trans (by decide +kernel)
    · exact v4481_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 74 79 Primitive.Addresses.material4481
    · exact v4481_mb_checked.trans (by decide +kernel)
    · exact v4481_mg_checked.trans (by decide +kernel)
  upper_error := v4481_upper_checked
  lower_error := reuse_lower_error 74 79 Primitive.Addresses.material4481

def v4482_pa : Scalar.QComplex := ((999997844676239806312200994626 : Int)/10^30,(-2076208774417174151287755655 : Int)/10^30)
theorem v4482_pa_checked : Scalar.distance (sourceCoefficient 74 80 1 0) v4482_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4482_pb : Scalar.QComplex := ((-895837414496718900524625 : Int)/10^30,(-431476590753032471635836025 : Int)/10^30)
theorem v4482_pb_checked : Scalar.distance (sourceCoefficient 74 80 1 1) v4482_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4482_pg : Scalar.QComplex := ((-93086229236040055478395 : Int)/10^30,(193266862469935588416 : Int)/10^30)
theorem v4482_pg_checked : Scalar.distance (sourceCoefficient 74 80 1 2) v4482_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4482_mb : Scalar.QComplex := ((-1268181945771113482262220 : Int)/10^30,(-431475657027236588652381823 : Int)/10^30)
theorem v4482_mb_checked : Scalar.distance (sourceCoefficient 74 80 3 1) v4482_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4482_mg : Scalar.QComplex := ((-93086027795184764868449 : Int)/10^30,(273596013890418725757 : Int)/10^30)
theorem v4482_mg_checked : Scalar.distance (sourceCoefficient 74 80 3 2) v4482_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4482_upper : Scalar.QComplex := ((999992771948925704211504326872 : Int)/10^30,(-3802111242963472835432071691 : Int)/10^30)
theorem v4482_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 74 80 5) 1) 14) v4482_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4482 : Material (74 : Basis) (80 : Basis) where
  plus := ![v4482_pa,v4482_pb,v4482_pg]
  minus := ![(Primitive.Addresses.material4482 1).one,v4482_mb,v4482_mg]
  upper := v4482_upper
  lower := (Primitive.Addresses.material4482 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4482_pa_checked.trans (by decide +kernel)
    · exact v4482_pb_checked.trans (by decide +kernel)
    · exact v4482_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 74 80 Primitive.Addresses.material4482
    · exact v4482_mb_checked.trans (by decide +kernel)
    · exact v4482_mg_checked.trans (by decide +kernel)
  upper_error := v4482_upper_checked
  lower_error := reuse_lower_error 74 80 Primitive.Addresses.material4482

def v4483_pa : Scalar.QComplex := ((999997789868779919565938875011 : Int)/10^30,(-2102440856595223738286131253 : Int)/10^30)
theorem v4483_pa_checked : Scalar.distance (sourceCoefficient 74 81 1 0) v4483_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4483_pb : Scalar.QComplex := ((-907155967684855688271740 : Int)/10^30,(-431476566822531787123837265 : Int)/10^30)
theorem v4483_pb_checked : Scalar.distance (sourceCoefficient 74 81 1 1) v4483_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4483_pg : Scalar.QComplex := ((-93086224103756271406947 : Int)/10^30,(195708713283853568781 : Int)/10^30)
theorem v4483_pg_checked : Scalar.distance (sourceCoefficient 74 81 1 2) v4483_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4483_mb : Scalar.QComplex := ((-1279500474093891333638530 : Int)/10^30,(-431475623329343181909507572 : Int)/10^30)
theorem v4483_mb_checked : Scalar.distance (sourceCoefficient 74 81 3 1) v4483_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4483_mg : Scalar.QComplex := ((-93086020555695616247719 : Int)/10^30,(276037859366194293833 : Int)/10^30)
theorem v4483_mg_checked : Scalar.distance (sourceCoefficient 74 81 3 2) v4483_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4483_upper : Scalar.QComplex := ((999992671867353363330579557350 : Int)/10^30,(-3828343191479213784454363549 : Int)/10^30)
theorem v4483_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 74 81 5) 1) 14) v4483_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4483 : Material (74 : Basis) (81 : Basis) where
  plus := ![v4483_pa,v4483_pb,v4483_pg]
  minus := ![(Primitive.Addresses.material4483 1).one,v4483_mb,v4483_mg]
  upper := v4483_upper
  lower := (Primitive.Addresses.material4483 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4483_pa_checked.trans (by decide +kernel)
    · exact v4483_pb_checked.trans (by decide +kernel)
    · exact v4483_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 74 81 Primitive.Addresses.material4483
    · exact v4483_mb_checked.trans (by decide +kernel)
    · exact v4483_mg_checked.trans (by decide +kernel)
  upper_error := v4483_upper_checked
  lower_error := reuse_lower_error 74 81 Primitive.Addresses.material4483

def v4484_pa : Scalar.QComplex := ((999997768920569210364272839935 : Int)/10^30,(-2112381093426052457697710418 : Int)/10^30)
theorem v4484_pa_checked : Scalar.distance (sourceCoefficient 74 82 1 0) v4484_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4484_pb : Scalar.QComplex := ((-911444956144652524500026 : Int)/10^30,(-431476557651014217526898894 : Int)/10^30)
theorem v4484_pb_checked : Scalar.distance (sourceCoefficient 74 82 1 1) v4484_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4484_pg : Scalar.QComplex := ((-93086222139433235479287 : Int)/10^30,(196634014411901338068 : Int)/10^30)
theorem v4484_pg_checked : Scalar.distance (sourceCoefficient 74 82 1 2) v4484_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4484_mb : Scalar.QComplex := ((-1283789453042095157083736 : Int)/10^30,(-431475610456625155352513507 : Int)/10^30)
theorem v4484_mb_checked : Scalar.distance (sourceCoefficient 74 82 3 1) v4484_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4484_mg : Scalar.QComplex := ((-93086017792880112237870 : Int)/10^30,(276963158454587854617 : Int)/10^30)
theorem v4484_mg_checked : Scalar.distance (sourceCoefficient 74 82 3 2) v4484_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4484_upper : Scalar.QComplex := ((999992633763226855258687909158 : Int)/10^30,(-3838283377350516129336812807 : Int)/10^30)
theorem v4484_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 74 82 5) 1) 14) v4484_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4484 : Material (74 : Basis) (82 : Basis) where
  plus := ![v4484_pa,v4484_pb,v4484_pg]
  minus := ![(Primitive.Addresses.material4484 1).one,v4484_mb,v4484_mg]
  upper := v4484_upper
  lower := (Primitive.Addresses.material4484 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4484_pa_checked.trans (by decide +kernel)
    · exact v4484_pb_checked.trans (by decide +kernel)
    · exact v4484_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 74 82 Primitive.Addresses.material4484
    · exact v4484_mb_checked.trans (by decide +kernel)
    · exact v4484_mg_checked.trans (by decide +kernel)
  upper_error := v4484_upper_checked
  lower_error := reuse_lower_error 74 82 Primitive.Addresses.material4484

def v4485_pa : Scalar.QComplex := ((999997740166417599775280278447 : Int)/10^30,(-2125949683777259413153694612 : Int)/10^30)
theorem v4485_pa_checked : Scalar.distance (sourceCoefficient 74 83 1 0) v4485_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4485_pb : Scalar.QComplex := ((-917299497429264558430108 : Int)/10^30,(-431476545039982464506002277 : Int)/10^30)
theorem v4485_pb_checked : Scalar.distance (sourceCoefficient 74 83 1 1) v4485_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4485_pg : Scalar.QComplex := ((-93086219440778333774966 : Int)/10^30,(197897065998578878320 : Int)/10^30)
theorem v4485_pg_checked : Scalar.distance (sourceCoefficient 74 83 1 2) v4485_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4485_mb : Scalar.QComplex := ((-1289643981264041481926757 : Int)/10^30,(-431475592793392648126149462 : Int)/10^30)
theorem v4485_mb_checked : Scalar.distance (sourceCoefficient 74 83 3 1) v4485_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4485_mg : Scalar.QComplex := ((-93086014004269581795152 : Int)/10^30,(278226207242155927573 : Int)/10^30)
theorem v4485_mg_checked : Scalar.distance (sourceCoefficient 74 83 3 2) v4485_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4485_upper : Scalar.QComplex := ((999992581590962057318755639846 : Int)/10^30,(-3851851897865844511637141890 : Int)/10^30)
theorem v4485_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 74 83 5) 1) 14) v4485_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4485 : Material (74 : Basis) (83 : Basis) where
  plus := ![v4485_pa,v4485_pb,v4485_pg]
  minus := ![(Primitive.Addresses.material4485 1).one,v4485_mb,v4485_mg]
  upper := v4485_upper
  lower := (Primitive.Addresses.material4485 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4485_pa_checked.trans (by decide +kernel)
    · exact v4485_pb_checked.trans (by decide +kernel)
    · exact v4485_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 74 83 Primitive.Addresses.material4485
    · exact v4485_mb_checked.trans (by decide +kernel)
    · exact v4485_mg_checked.trans (by decide +kernel)
  upper_error := v4485_upper_checked
  lower_error := reuse_lower_error 74 83 Primitive.Addresses.material4485

def v4486_pa : Scalar.QComplex := ((999997664845174826545287412156 : Int)/10^30,(-2161088660235588736616743516 : Int)/10^30)
theorem v4486_pa_checked : Scalar.distance (sourceCoefficient 74 84 1 0) v4486_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4486_pb : Scalar.QComplex := ((-932461174441443916362534 : Int)/10^30,(-431476511888495183812911052 : Int)/10^30)
theorem v4486_pb_checked : Scalar.distance (sourceCoefficient 74 84 1 1) v4486_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4486_pg : Scalar.QComplex := ((-93086212359054988028778 : Int)/10^30,(201168027711926228243 : Int)/10^30)
theorem v4486_pg_checked : Scalar.distance (sourceCoefficient 74 84 1 2) v4486_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4486_mb : Scalar.QComplex := ((-1304805624022595129677236 : Int)/10^30,(-431475546558073306319885395 : Int)/10^30)
theorem v4486_mb_checked : Scalar.distance (sourceCoefficient 74 84 3 1) v4486_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4486_mg : Scalar.QComplex := ((-93086004099856232926297 : Int)/10^30,(281497161626366442883 : Int)/10^30)
theorem v4486_mg_checked : Scalar.distance (sourceCoefficient 74 84 3 2) v4486_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4486_upper : Scalar.QComplex := ((999992445623145882198311564431 : Int)/10^30,(-3886990691991164177721813646 : Int)/10^30)
theorem v4486_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 74 84 5) 1) 14) v4486_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4486 : Material (74 : Basis) (84 : Basis) where
  plus := ![v4486_pa,v4486_pb,v4486_pg]
  minus := ![(Primitive.Addresses.material4486 1).one,v4486_mb,v4486_mg]
  upper := v4486_upper
  lower := (Primitive.Addresses.material4486 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4486_pa_checked.trans (by decide +kernel)
    · exact v4486_pb_checked.trans (by decide +kernel)
    · exact v4486_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 74 84 Primitive.Addresses.material4486
    · exact v4486_mb_checked.trans (by decide +kernel)
    · exact v4486_mg_checked.trans (by decide +kernel)
  upper_error := v4486_upper_checked
  lower_error := reuse_lower_error 74 84 Primitive.Addresses.material4486

def v4487_pa : Scalar.QComplex := ((999997490871400414891853128864 : Int)/10^30,(-2240145286235668920306082588 : Int)/10^30)
theorem v4487_pa_checked : Scalar.distance (sourceCoefficient 74 85 1 0) v4487_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4487_pb : Scalar.QComplex := ((-966572326583728670187684 : Int)/10^30,(-431476434706465233225045365 : Int)/10^30)
theorem v4487_pb_checked : Scalar.distance (sourceCoefficient 74 85 1 1) v4487_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4487_pg : Scalar.QComplex := ((-93086195936178087318299 : Int)/10^30,(208527126261415514267 : Int)/10^30)
theorem v4487_pg_checked : Scalar.distance (sourceCoefficient 74 85 1 2) v4487_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4487_mb : Scalar.QComplex := ((-1338916696859123286493756 : Int)/10^30,(-431475439939684104599428745 : Int)/10^30)
theorem v4487_mb_checked : Scalar.distance (sourceCoefficient 74 85 3 1) v4487_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4487_mg : Scalar.QComplex := ((-93085981326414840489180 : Int)/10^30,(288856243263523905118 : Int)/10^30)
theorem v4487_mg_checked : Scalar.distance (sourceCoefficient 74 85 3 2) v4487_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4487_upper : Scalar.QComplex := ((999992135205066068993513059916 : Int)/10^30,(-3966046899982734720945329573 : Int)/10^30)
theorem v4487_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 74 85 5) 1) 14) v4487_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4487 : Material (74 : Basis) (85 : Basis) where
  plus := ![v4487_pa,v4487_pb,v4487_pg]
  minus := ![(Primitive.Addresses.material4487 1).one,v4487_mb,v4487_mg]
  upper := v4487_upper
  lower := (Primitive.Addresses.material4487 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4487_pa_checked.trans (by decide +kernel)
    · exact v4487_pb_checked.trans (by decide +kernel)
    · exact v4487_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 74 85 Primitive.Addresses.material4487
    · exact v4487_mb_checked.trans (by decide +kernel)
    · exact v4487_mg_checked.trans (by decide +kernel)
  upper_error := v4487_upper_checked
  lower_error := reuse_lower_error 74 85 Primitive.Addresses.material4487

def v4488_pa : Scalar.QComplex := ((999997458093323027753876683391 : Int)/10^30,(-2254729893502753426991899248 : Int)/10^30)
theorem v4488_pa_checked : Scalar.distance (sourceCoefficient 74 86 1 0) v4488_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4488_pb : Scalar.QComplex := ((-972865255616970972065606 : Int)/10^30,(-431476420074834957677700129 : Int)/10^30)
theorem v4488_pb_checked : Scalar.distance (sourceCoefficient 74 86 1 1) v4488_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4488_pg : Scalar.QComplex := ((-93086192832276022953570 : Int)/10^30,(209884755158755019357 : Int)/10^30)
theorem v4488_pg_checked : Scalar.distance (sourceCoefficient 74 86 1 2) v4488_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4488_mb : Scalar.QComplex := ((-1345209610922782564598579 : Int)/10^30,(-431475419877544944391127942 : Int)/10^30)
theorem v4488_mb_checked : Scalar.distance (sourceCoefficient 74 86 3 1) v4488_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4488_mg : Scalar.QComplex := ((-93085977050941338780766 : Int)/10^30,(290213868976828438036 : Int)/10^30)
theorem v4488_mg_checked : Scalar.distance (sourceCoefficient 74 86 3 2) v4488_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4488_upper : Scalar.QComplex := ((999992077255328463199301774323 : Int)/10^30,(-3980631428955771965377985101 : Int)/10^30)
theorem v4488_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 74 86 5) 1) 14) v4488_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4488 : Material (74 : Basis) (86 : Basis) where
  plus := ![v4488_pa,v4488_pb,v4488_pg]
  minus := ![(Primitive.Addresses.material4488 1).one,v4488_mb,v4488_mg]
  upper := v4488_upper
  lower := (Primitive.Addresses.material4488 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4488_pa_checked.trans (by decide +kernel)
    · exact v4488_pb_checked.trans (by decide +kernel)
    · exact v4488_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 74 86 Primitive.Addresses.material4488
    · exact v4488_mb_checked.trans (by decide +kernel)
    · exact v4488_mg_checked.trans (by decide +kernel)
  upper_error := v4488_upper_checked
  lower_error := reuse_lower_error 74 86 Primitive.Addresses.material4488

def v4489_pa : Scalar.QComplex := ((999997455915336770140384326876 : Int)/10^30,(-2255695647487254772966411568 : Int)/10^30)
theorem v4489_pa_checked : Scalar.distance (sourceCoefficient 74 87 1 0) v4489_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4489_pb : Scalar.QComplex := ((-973281956672671391469603 : Int)/10^30,(-431476419101647305500986717 : Int)/10^30)
theorem v4489_pb_checked : Scalar.distance (sourceCoefficient 74 87 1 1) v4489_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4489_pg : Scalar.QComplex := ((-93086192625928386643831 : Int)/10^30,(209974653740763101616 : Int)/10^30)
theorem v4489_pg_checked : Scalar.distance (sourceCoefficient 74 87 1 2) v4489_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4489_mb : Scalar.QComplex := ((-1345626310983509023702539 : Int)/10^30,(-431475418544763411026058061 : Int)/10^30)
theorem v4489_mb_checked : Scalar.distance (sourceCoefficient 74 87 3 1) v4489_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4489_mg : Scalar.QComplex := ((-93085976767015351912540 : Int)/10^30,(290303767347294453062 : Int)/10^30)
theorem v4489_mg_checked : Scalar.distance (sourceCoefficient 74 87 3 2) v4489_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4489_upper : Scalar.QComplex := ((999992073410541684708255280158 : Int)/10^30,(-3981597177742889501598819762 : Int)/10^30)
theorem v4489_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 74 87 5) 1) 14) v4489_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4489 : Material (74 : Basis) (87 : Basis) where
  plus := ![v4489_pa,v4489_pb,v4489_pg]
  minus := ![(Primitive.Addresses.material4489 1).one,v4489_mb,v4489_mg]
  upper := v4489_upper
  lower := (Primitive.Addresses.material4489 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4489_pa_checked.trans (by decide +kernel)
    · exact v4489_pb_checked.trans (by decide +kernel)
    · exact v4489_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 74 87 Primitive.Addresses.material4489
    · exact v4489_mb_checked.trans (by decide +kernel)
    · exact v4489_mg_checked.trans (by decide +kernel)
  upper_error := v4489_upper_checked
  lower_error := reuse_lower_error 74 87 Primitive.Addresses.material4489

def v4490_pa : Scalar.QComplex := ((999997429320128927134352205686 : Int)/10^30,(-2267455210969057213580948087 : Int)/10^30)
theorem v4490_pa_checked : Scalar.distance (sourceCoefficient 74 88 1 0) v4490_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4490_pb : Scalar.QComplex := ((-978355942975098622098855 : Int)/10^30,(-431476407208521638936817353 : Int)/10^30)
theorem v4490_pb_checked : Scalar.distance (sourceCoefficient 74 88 1 1) v4490_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4490_pg : Scalar.QComplex := ((-93086190105197757134848 : Int)/10^30,(211069309414912060667 : Int)/10^30)
theorem v4490_pg_checked : Scalar.distance (sourceCoefficient 74 88 1 2) v4490_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4490_mb : Scalar.QComplex := ((-1350700285133427457559396 : Int)/10^30,(-431475402273020517681273908 : Int)/10^30)
theorem v4490_mb_checked : Scalar.distance (sourceCoefficient 74 88 3 1) v4490_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4490_mg : Scalar.QComplex := ((-93085973301647115657629 : Int)/10^30,(291398420438576072618 : Int)/10^30)
theorem v4490_mg_checked : Scalar.distance (sourceCoefficient 74 88 3 2) v4490_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4490_upper : Scalar.QComplex := ((999992026519433701814734593029 : Int)/10^30,(-3993356677809287472811660627 : Int)/10^30)
theorem v4490_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 74 88 5) 1) 14) v4490_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4490 : Material (74 : Basis) (88 : Basis) where
  plus := ![v4490_pa,v4490_pb,v4490_pg]
  minus := ![(Primitive.Addresses.material4490 1).one,v4490_mb,v4490_mg]
  upper := v4490_upper
  lower := (Primitive.Addresses.material4490 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4490_pa_checked.trans (by decide +kernel)
    · exact v4490_pb_checked.trans (by decide +kernel)
    · exact v4490_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 74 88 Primitive.Addresses.material4490
    · exact v4490_mb_checked.trans (by decide +kernel)
    · exact v4490_mg_checked.trans (by decide +kernel)
  upper_error := v4490_upper_checked
  lower_error := reuse_lower_error 74 88 Primitive.Addresses.material4490

def v4491_pa : Scalar.QComplex := ((999997392708507971829470046346 : Int)/10^30,(-2283544653841351239326040283 : Int)/10^30)
theorem v4491_pa_checked : Scalar.distance (sourceCoefficient 74 89 1 0) v4491_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4491_pb : Scalar.QComplex := ((-985298174446658048651624 : Int)/10^30,(-431476390807448557847903105 : Int)/10^30)
theorem v4491_pb_checked : Scalar.distance (sourceCoefficient 74 89 1 1) v4491_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4491_pg : Scalar.QComplex := ((-93086186632001542820184 : Int)/10^30,(212567018054163038700 : Int)/10^30)
theorem v4491_pg_checked : Scalar.distance (sourceCoefficient 74 89 1 2) v4491_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4491_mb : Scalar.QComplex := ((-1357642499866689439529467 : Int)/10^30,(-431475379881120450004401728 : Int)/10^30)
theorem v4491_mb_checked : Scalar.distance (sourceCoefficient 74 89 3 1) v4491_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4491_mg : Scalar.QComplex := ((-93085968535997093192145 : Int)/10^30,(292896125522949769589 : Int)/10^30)
theorem v4491_mg_checked : Scalar.distance (sourceCoefficient 74 89 3 2) v4491_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4491_upper : Scalar.QComplex := ((999991962138948500494500306945 : Int)/10^30,(-4009446033529909950451389869 : Int)/10^30)
theorem v4491_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 74 89 5) 1) 14) v4491_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4491 : Material (74 : Basis) (89 : Basis) where
  plus := ![v4491_pa,v4491_pb,v4491_pg]
  minus := ![(Primitive.Addresses.material4491 1).one,v4491_mb,v4491_mg]
  upper := v4491_upper
  lower := (Primitive.Addresses.material4491 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4491_pa_checked.trans (by decide +kernel)
    · exact v4491_pb_checked.trans (by decide +kernel)
    · exact v4491_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 74 89 Primitive.Addresses.material4491
    · exact v4491_mb_checked.trans (by decide +kernel)
    · exact v4491_mg_checked.trans (by decide +kernel)
  upper_error := v4491_upper_checked
  lower_error := reuse_lower_error 74 89 Primitive.Addresses.material4491

def v4492_pa : Scalar.QComplex := ((999997332529624405738533862338 : Int)/10^30,(-2309747526417187931022150475 : Int)/10^30)
theorem v4492_pa_checked : Scalar.distance (sourceCoefficient 74 90 1 0) v4492_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4492_pb : Scalar.QComplex := ((-996604122356362368102643 : Int)/10^30,(-431476363778290742889524090 : Int)/10^30)
theorem v4492_pb_checked : Scalar.distance (sourceCoefficient 74 90 1 1) v4492_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4492_pg : Scalar.QComplex := ((-93086180915464192520575 : Int)/10^30,(215006149635650988725 : Int)/10^30)
theorem v4492_pg_checked : Scalar.distance (sourceCoefficient 74 90 1 2) v4492_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4492_mb : Scalar.QComplex := ((-1368948420241726798621054 : Int)/10^30,(-431475343095448854153366837 : Int)/10^30)
theorem v4492_mb_checked : Scalar.distance (sourceCoefficient 74 90 3 1) v4492_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4492_mg : Scalar.QComplex := ((-93085960714601171004993 : Int)/10^30,(295335251263123287982 : Int)/10^30)
theorem v4492_mg_checked : Scalar.distance (sourceCoefficient 74 90 3 2) v4492_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4492_upper : Scalar.QComplex := ((999991856736373603918544328995 : Int)/10^30,(-4035648763216352296667387690 : Int)/10^30)
theorem v4492_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 74 90 5) 1) 14) v4492_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4492 : Material (74 : Basis) (90 : Basis) where
  plus := ![v4492_pa,v4492_pb,v4492_pg]
  minus := ![(Primitive.Addresses.material4492 1).one,v4492_mb,v4492_mg]
  upper := v4492_upper
  lower := (Primitive.Addresses.material4492 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4492_pa_checked.trans (by decide +kernel)
    · exact v4492_pb_checked.trans (by decide +kernel)
    · exact v4492_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 74 90 Primitive.Addresses.material4492
    · exact v4492_mb_checked.trans (by decide +kernel)
    · exact v4492_mg_checked.trans (by decide +kernel)
  upper_error := v4492_upper_checked
  lower_error := reuse_lower_error 74 90 Primitive.Addresses.material4492

def v4493_pa : Scalar.QComplex := ((999997298326332887721170655432 : Int)/10^30,(-2324508557778171332232953950 : Int)/10^30)
theorem v4493_pa_checked : Scalar.distance (sourceCoefficient 74 91 1 0) v4493_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4493_pb : Scalar.QComplex := ((-1002973173989395172130677 : Int)/10^30,(-431476348377847533178837584 : Int)/10^30)
theorem v4493_pb_checked : Scalar.distance (sourceCoefficient 74 91 1 1) v4493_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4493_pg : Scalar.QComplex := ((-93086177662296701956523 : Int)/10^30,(216380201175559535321 : Int)/10^30)
theorem v4493_pg_checked : Scalar.distance (sourceCoefficient 74 91 1 2) v4493_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4493_mb : Scalar.QComplex := ((-1375317456213381719865521 : Int)/10^30,(-431475322198806670861338373 : Int)/10^30)
theorem v4493_mb_checked : Scalar.distance (sourceCoefficient 74 91 3 1) v4493_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4493_mg : Scalar.QComplex := ((-93085956275690297786877 : Int)/10^30,(296709299484072621881 : Int)/10^30)
theorem v4493_mg_checked : Scalar.distance (sourceCoefficient 74 91 3 2) v4493_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4493_upper : Scalar.QComplex := ((999991797056932008933258636051 : Int)/10^30,(-4050409713560735176510633025 : Int)/10^30)
theorem v4493_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 74 91 5) 1) 14) v4493_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4493 : Material (74 : Basis) (91 : Basis) where
  plus := ![v4493_pa,v4493_pb,v4493_pg]
  minus := ![(Primitive.Addresses.material4493 1).one,v4493_mb,v4493_mg]
  upper := v4493_upper
  lower := (Primitive.Addresses.material4493 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4493_pa_checked.trans (by decide +kernel)
    · exact v4493_pb_checked.trans (by decide +kernel)
    · exact v4493_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 74 91 Primitive.Addresses.material4493
    · exact v4493_mb_checked.trans (by decide +kernel)
    · exact v4493_mg_checked.trans (by decide +kernel)
  upper_error := v4493_upper_checked
  lower_error := reuse_lower_error 74 91 Primitive.Addresses.material4493

def v4494_pa : Scalar.QComplex := ((999997223533499261879603930853 : Int)/10^30,(-2356464574889682289440531521 : Int)/10^30)
theorem v4494_pa_checked : Scalar.distance (sourceCoefficient 74 92 1 0) v4494_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4494_pb : Scalar.QComplex := ((-1016761473282203440082633 : Int)/10^30,(-431476314608138384637316635 : Int)/10^30)
theorem v4494_pb_checked : Scalar.distance (sourceCoefficient 74 92 1 1) v4494_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4494_pg : Scalar.QComplex := ((-93086170538480004207812 : Int)/10^30,(219354872317522514332 : Int)/10^30)
theorem v4494_pg_checked : Scalar.distance (sourceCoefficient 74 92 1 2) v4494_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4494_mb : Scalar.QComplex := ((-1389105721230437940746016 : Int)/10^30,(-431475276530428808579822328 : Int)/10^30)
theorem v4494_mb_checked : Scalar.distance (sourceCoefficient 74 92 3 1) v4494_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4494_mg : Scalar.QComplex := ((-93085946584869031261524 : Int)/10^30,(299683963370896620188 : Int)/10^30)
theorem v4494_mg_checked : Scalar.distance (sourceCoefficient 74 92 3 2) v4494_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4494_upper : Scalar.QComplex := ((999991667111023270990080412044 : Int)/10^30,(-4082365553991866778245139159 : Int)/10^30)
theorem v4494_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 74 92 5) 1) 14) v4494_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4494 : Material (74 : Basis) (92 : Basis) where
  plus := ![v4494_pa,v4494_pb,v4494_pg]
  minus := ![(Primitive.Addresses.material4494 1).one,v4494_mb,v4494_mg]
  upper := v4494_upper
  lower := (Primitive.Addresses.material4494 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4494_pa_checked.trans (by decide +kernel)
    · exact v4494_pb_checked.trans (by decide +kernel)
    · exact v4494_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 74 92 Primitive.Addresses.material4494
    · exact v4494_mb_checked.trans (by decide +kernel)
    · exact v4494_mg_checked.trans (by decide +kernel)
  upper_error := v4494_upper_checked
  lower_error := reuse_lower_error 74 92 Primitive.Addresses.material4494

def v4495_pa : Scalar.QComplex := ((999997133443964816690532304397 : Int)/10^30,(-2394390079586681734282291163 : Int)/10^30)
theorem v4495_pa_checked : Scalar.distance (sourceCoefficient 74 93 1 0) v4495_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4495_pb : Scalar.QComplex := ((-1033125470998634527878764 : Int)/10^30,(-431476273767772024980923916 : Int)/10^30)
theorem v4495_pb_checked : Scalar.distance (sourceCoefficient 74 93 1 1) v4495_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4495_pg : Scalar.QComplex := ((-93086161939998225519896 : Int)/10^30,(222885221608908251572 : Int)/10^30)
theorem v4495_pg_checked : Scalar.distance (sourceCoefficient 74 93 1 2) v4495_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4495_mb : Scalar.QComplex := ((-1405469677610408020509913 : Int)/10^30,(-431475221568684633476452043 : Int)/10^30)
theorem v4495_mb_checked : Scalar.distance (sourceCoefficient 74 93 3 1) v4495_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4495_mg : Scalar.QComplex := ((-93085934939858016745141 : Int)/10^30,(303214303927669457548 : Int)/10^30)
theorem v4495_mg_checked : Scalar.distance (sourceCoefficient 74 93 3 2) v4495_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4495_upper : Scalar.QComplex := ((999991511565642471468678512632 : Int)/10^30,(-4120290846716918425963279587 : Int)/10^30)
theorem v4495_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 74 93 5) 1) 14) v4495_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4495 : Material (74 : Basis) (93 : Basis) where
  plus := ![v4495_pa,v4495_pb,v4495_pg]
  minus := ![(Primitive.Addresses.material4495 1).one,v4495_mb,v4495_mg]
  upper := v4495_upper
  lower := (Primitive.Addresses.material4495 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4495_pa_checked.trans (by decide +kernel)
    · exact v4495_pb_checked.trans (by decide +kernel)
    · exact v4495_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 74 93 Primitive.Addresses.material4495
    · exact v4495_mb_checked.trans (by decide +kernel)
    · exact v4495_mg_checked.trans (by decide +kernel)
  upper_error := v4495_upper_checked
  lower_error := reuse_lower_error 74 93 Primitive.Addresses.material4495

def v4496_pa : Scalar.QComplex := ((999997025175290702101236114858 : Int)/10^30,(-2439188506248286354129931567 : Int)/10^30)
theorem v4496_pa_checked : Scalar.distance (sourceCoefficient 74 94 1 0) v4496_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4496_pb : Scalar.QComplex := ((-1052454978291876969680593 : Int)/10^30,(-431476224460231391708744784 : Int)/10^30)
theorem v4496_pb_checked : Scalar.distance (sourceCoefficient 74 94 1 1) v4496_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4496_pg : Scalar.QComplex := ((-93086151582051957782793 : Int)/10^30,(227055346479681958468 : Int)/10^30)
theorem v4496_pg_checked : Scalar.distance (sourceCoefficient 74 94 1 2) v4496_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4496_mb : Scalar.QComplex := ((-1424799135156204657592218 : Int)/10^30,(-431475155580668134278348071 : Int)/10^30)
theorem v4496_mb_checked : Scalar.distance (sourceCoefficient 74 94 3 1) v4496_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4496_mg : Scalar.QComplex := ((-93085920983285657719248 : Int)/10^30,(307384418307273966459 : Int)/10^30)
theorem v4496_mg_checked : Scalar.distance (sourceCoefficient 74 94 3 2) v4496_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4496_upper : Scalar.QComplex := ((999991325979109273941648439858 : Int)/10^30,(-4165089019794619461818295729 : Int)/10^30)
theorem v4496_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 74 94 5) 1) 14) v4496_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4496 : Material (74 : Basis) (94 : Basis) where
  plus := ![v4496_pa,v4496_pb,v4496_pg]
  minus := ![(Primitive.Addresses.material4496 1).one,v4496_mb,v4496_mg]
  upper := v4496_upper
  lower := (Primitive.Addresses.material4496 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4496_pa_checked.trans (by decide +kernel)
    · exact v4496_pb_checked.trans (by decide +kernel)
    · exact v4496_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 74 94 Primitive.Addresses.material4496
    · exact v4496_mb_checked.trans (by decide +kernel)
    · exact v4496_mg_checked.trans (by decide +kernel)
  upper_error := v4496_upper_checked
  lower_error := reuse_lower_error 74 94 Primitive.Addresses.material4496

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
