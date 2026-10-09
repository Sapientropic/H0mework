import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B000
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B001

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v17_pa : Scalar.QComplex := ((999969913552489581127618803635 : Int)/10^30,(7757060643472754723776968202 : Int)/10^30)
theorem v17_pa_checked : Scalar.distance (sourceCoefficient 0 18 1 0) v17_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v17_pb : Scalar.QComplex := ((3346962206127825124407747 : Int)/10^30,(-431460015816859244740657140 : Int)/10^30)
theorem v17_pb_checked : Scalar.distance (sourceCoefficient 0 18 1 1) v17_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v17_pg : Scalar.QComplex := ((-93083141303060648013525 : Int)/10^30,(-722073296593121606974 : Int)/10^30)
theorem v17_pg_checked : Scalar.distance (sourceCoefficient 0 18 1 2) v17_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v17_mb : Scalar.QComplex := ((2974630398488636343588933 : Int)/10^30,(-431462743442218965617382074 : Int)/10^30)
theorem v17_mb_checked : Scalar.distance (sourceCoefficient 0 18 3 1) v17_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v17_mg : Scalar.QComplex := ((-93083729760687016989907 : Int)/10^30,(-641746469096750028559 : Int)/10^30)
theorem v17_mg_checked : Scalar.distance (sourceCoefficient 0 18 3 2) v17_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v17_upper : Scalar.QComplex := ((999981812197723651705679929571 : Int)/10^30,(6031191736012456195269603766 : Int)/10^30)
theorem v17_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 18 5) 1) 14) v17_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material17 : Material (0 : Basis) (18 : Basis) where
  plus := ![v17_pa,v17_pb,v17_pg]
  minus := ![(Primitive.Addresses.material17 1).one,v17_mb,v17_mg]
  upper := v17_upper
  lower := (Primitive.Addresses.material17 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v17_pa_checked.trans (by decide +kernel)
    · exact v17_pb_checked.trans (by decide +kernel)
    · exact v17_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 18 Primitive.Addresses.material17
    · exact v17_mb_checked.trans (by decide +kernel)
    · exact v17_mg_checked.trans (by decide +kernel)
  upper_error := v17_upper_checked
  lower_error := reuse_lower_error 0 18 Primitive.Addresses.material17

def v18_pa : Scalar.QComplex := ((999970034840817851732252839040 : Int)/10^30,(7741409461689242284752237196 : Int)/10^30)
theorem v18_pa_checked : Scalar.distance (sourceCoefficient 0 19 1 0) v18_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v18_pb : Scalar.QComplex := ((3340209005459952077692897 : Int)/10^30,(-431460050278306976926790266 : Int)/10^30)
theorem v18_pb_checked : Scalar.distance (sourceCoefficient 0 19 1 1) v18_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v18_pg : Scalar.QComplex := ((-93083150665540531549855 : Int)/10^30,(-720616376670496955412 : Int)/10^30)
theorem v18_pg_checked : Scalar.distance (sourceCoefficient 0 19 1 2) v18_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v18_mb : Scalar.QComplex := ((2967877170596611235153777 : Int)/10^30,(-431462772075945842724515067 : Int)/10^30)
theorem v18_mb_checked : Scalar.distance (sourceCoefficient 0 19 3 1) v18_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v18_mg : Scalar.QComplex := ((-93083737865907138459505 : Int)/10^30,(-640289541637204779669 : Int)/10^30)
theorem v18_mg_checked : Scalar.distance (sourceCoefficient 0 19 3 2) v18_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v18_upper : Scalar.QComplex := ((999981906473351383370443434922 : Int)/10^30,(6015540368206889101950485030 : Int)/10^30)
theorem v18_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 19 5) 1) 14) v18_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material18 : Material (0 : Basis) (19 : Basis) where
  plus := ![v18_pa,v18_pb,v18_pg]
  minus := ![(Primitive.Addresses.material18 1).one,v18_mb,v18_mg]
  upper := v18_upper
  lower := (Primitive.Addresses.material18 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v18_pa_checked.trans (by decide +kernel)
    · exact v18_pb_checked.trans (by decide +kernel)
    · exact v18_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 19 Primitive.Addresses.material18
    · exact v18_mb_checked.trans (by decide +kernel)
    · exact v18_mg_checked.trans (by decide +kernel)
  upper_error := v18_upper_checked
  lower_error := reuse_lower_error 0 19 Primitive.Addresses.material18

def v19_pa : Scalar.QComplex := ((999970056554889101800902225013 : Int)/10^30,(7738604112622074739743459531 : Int)/10^30)
theorem v19_pa_checked : Scalar.distance (sourceCoefficient 0 20 1 0) v19_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v19_pb : Scalar.QComplex := ((3338998548321207907669054 : Int)/10^30,(-431460056440350760831388105 : Int)/10^30)
theorem v19_pb_checked : Scalar.distance (sourceCoefficient 0 20 1 1) v19_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v19_pg : Scalar.QComplex := ((-93083152340878366839243 : Int)/10^30,(-720355235438401130994 : Int)/10^30)
theorem v19_pg_checked : Scalar.distance (sourceCoefficient 0 20 1 2) v19_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v19_mb : Scalar.QComplex := ((2966666708591009321148554 : Int)/10^30,(-431462777193417338448138256 : Int)/10^30)
theorem v19_mb_checked : Scalar.distance (sourceCoefficient 0 20 3 1) v19_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v19_mg : Scalar.QComplex := ((-93083739315891228009845 : Int)/10^30,(-640028399056602673265 : Int)/10^30)
theorem v19_mg_checked : Scalar.distance (sourceCoefficient 0 20 3 2) v19_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v19_upper : Scalar.QComplex := ((999981923345612302228831315331 : Int)/10^30,(6012734985841442360574871358 : Int)/10^30)
theorem v19_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 20 5) 1) 14) v19_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material19 : Material (0 : Basis) (20 : Basis) where
  plus := ![v19_pa,v19_pb,v19_pg]
  minus := ![(Primitive.Addresses.material19 1).one,v19_mb,v19_mg]
  upper := v19_upper
  lower := (Primitive.Addresses.material19 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v19_pa_checked.trans (by decide +kernel)
    · exact v19_pb_checked.trans (by decide +kernel)
    · exact v19_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 20 Primitive.Addresses.material19
    · exact v19_mb_checked.trans (by decide +kernel)
    · exact v19_mg_checked.trans (by decide +kernel)
  upper_error := v19_upper_checked
  lower_error := reuse_lower_error 0 20 Primitive.Addresses.material19

def v20_pa : Scalar.QComplex := ((999970465364256619130649497506 : Int)/10^30,(7685596866350280052930190857 : Int)/10^30)
theorem v20_pa_checked : Scalar.distance (sourceCoefficient 0 21 1 0) v20_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v20_pb : Scalar.QComplex := ((3316126886642905397660541 : Int)/10^30,(-431460172021478712294127220 : Int)/10^30)
theorem v20_pb_checked : Scalar.distance (sourceCoefficient 0 21 1 1) v20_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v20_pg : Scalar.QComplex := ((-93083183835832003326210 : Int)/10^30,(-715420955695907145868 : Int)/10^30)
theorem v20_pg_checked : Scalar.distance (sourceCoefficient 0 21 1 2) v20_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v20_mb : Scalar.QComplex := ((2943794955687563899199318 : Int)/10^30,(-431462873037288326802385629 : Int)/10^30)
theorem v20_mb_checked : Scalar.distance (sourceCoefficient 0 21 3 1) v20_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v20_mg : Scalar.QComplex := ((-93083766552771951423847 : Int)/10^30,(-635094093972640035760 : Int)/10^30)
theorem v20_mg_checked : Scalar.distance (sourceCoefficient 0 21 3 2) v20_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v20_upper : Scalar.QComplex := ((999982240668672660727804501437 : Int)/10^30,(5959727112949832888256189277 : Int)/10^30)
theorem v20_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 21 5) 1) 14) v20_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material20 : Material (0 : Basis) (21 : Basis) where
  plus := ![v20_pa,v20_pb,v20_pg]
  minus := ![(Primitive.Addresses.material20 1).one,v20_mb,v20_mg]
  upper := v20_upper
  lower := (Primitive.Addresses.material20 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v20_pa_checked.trans (by decide +kernel)
    · exact v20_pb_checked.trans (by decide +kernel)
    · exact v20_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 21 Primitive.Addresses.material20
    · exact v20_mb_checked.trans (by decide +kernel)
    · exact v20_mg_checked.trans (by decide +kernel)
  upper_error := v20_upper_checked
  lower_error := reuse_lower_error 0 21 Primitive.Addresses.material20

def v21_pa : Scalar.QComplex := ((999970476077760779070272327887 : Int)/10^30,(7684202809430362236289180978 : Int)/10^30)
theorem v21_pa_checked : Scalar.distance (sourceCoefficient 0 22 1 0) v21_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v21_pb : Scalar.QComplex := ((3315525376508258195079685 : Int)/10^30,(-431460175039372237861194575 : Int)/10^30)
theorem v21_pb_checked : Scalar.distance (sourceCoefficient 0 22 1 1) v21_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v21_pg : Scalar.QComplex := ((-93083184660010881720812 : Int)/10^30,(-715291187276572368339 : Int)/10^30)
theorem v21_pg_checked : Scalar.distance (sourceCoefficient 0 22 1 2) v21_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v21_mb : Scalar.QComplex := ((2943193443172580218433212 : Int)/10^30,(-431462875536104573480031958 : Int)/10^30)
theorem v21_mb_checked : Scalar.distance (sourceCoefficient 0 22 3 1) v21_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v21_mg : Scalar.QComplex := ((-93083767264966221605719 : Int)/10^30,(-634964324890394719043 : Int)/10^30)
theorem v21_mg_checked : Scalar.distance (sourceCoefficient 0 22 3 2) v21_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v21_upper : Scalar.QComplex := ((999982248976145088239188451946 : Int)/10^30,(5958333039615662837852988318 : Int)/10^30)
theorem v21_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 22 5) 1) 14) v21_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material21 : Material (0 : Basis) (22 : Basis) where
  plus := ![v21_pa,v21_pb,v21_pg]
  minus := ![(Primitive.Addresses.material21 1).one,v21_mb,v21_mg]
  upper := v21_upper
  lower := (Primitive.Addresses.material21 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v21_pa_checked.trans (by decide +kernel)
    · exact v21_pb_checked.trans (by decide +kernel)
    · exact v21_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 22 Primitive.Addresses.material21
    · exact v21_mb_checked.trans (by decide +kernel)
    · exact v21_mg_checked.trans (by decide +kernel)
  upper_error := v21_upper_checked
  lower_error := reuse_lower_error 0 22 Primitive.Addresses.material21

def v22_pa : Scalar.QComplex := ((999970555239129197557164061740 : Int)/10^30,(7673894366464927234901986833 : Int)/10^30)
theorem v22_pa_checked : Scalar.distance (sourceCoefficient 0 23 1 0) v22_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v22_pb : Scalar.QComplex := ((3311077471457348271761336 : Int)/10^30,(-431460197320675356352710393 : Int)/10^30)
theorem v22_pb_checked : Scalar.distance (sourceCoefficient 0 23 1 1) v22_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v22_pg : Scalar.QComplex := ((-93083190747903210956237 : Int)/10^30,(-714331606416248069953 : Int)/10^30)
theorem v22_pg_checked : Scalar.distance (sourceCoefficient 0 23 1 2) v22_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v22_mb : Scalar.QComplex := ((2938745520550067546253794 : Int)/10^30,(-431462893979057662895861704 : Int)/10^30)
theorem v22_mb_checked : Scalar.distance (sourceCoefficient 0 23 3 1) v22_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v22_mg : Scalar.QComplex := ((-93083772524781219498354 : Int)/10^30,(-634004739133789338330 : Int)/10^30)
theorem v22_mg_checked : Scalar.distance (sourceCoefficient 0 23 3 2) v22_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v22_upper : Scalar.QComplex := ((999982310345958221466596872501 : Int)/10^30,(5948024475378102291644423094 : Int)/10^30)
theorem v22_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 23 5) 1) 14) v22_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material22 : Material (0 : Basis) (23 : Basis) where
  plus := ![v22_pa,v22_pb,v22_pg]
  minus := ![(Primitive.Addresses.material22 1).one,v22_mb,v22_mg]
  upper := v22_upper
  lower := (Primitive.Addresses.material22 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v22_pa_checked.trans (by decide +kernel)
    · exact v22_pb_checked.trans (by decide +kernel)
    · exact v22_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 23 Primitive.Addresses.material22
    · exact v22_mb_checked.trans (by decide +kernel)
    · exact v22_mg_checked.trans (by decide +kernel)
  upper_error := v22_upper_checked
  lower_error := reuse_lower_error 0 23 Primitive.Addresses.material22

def v23_pa : Scalar.QComplex := ((999970944895461992637549840045 : Int)/10^30,(7622949880257314820770324761 : Int)/10^30)
theorem v23_pa_checked : Scalar.distance (sourceCoefficient 0 24 1 0) v23_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v23_pb : Scalar.QComplex := ((3289095857080077643894743 : Int)/10^30,(-431460306537538657393001570 : Int)/10^30)
theorem v23_pb_checked : Scalar.distance (sourceCoefficient 0 24 1 1) v23_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v23_pg : Scalar.QComplex := ((-93083220664903936573322 : Int)/10^30,(-709589343014035004507 : Int)/10^30)
theorem v23_pg_checked : Scalar.distance (sourceCoefficient 0 24 1 2) v23_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v23_mb : Scalar.QComplex := ((2916763820108322476576298 : Int)/10^30,(-431462984226737105082398831 : Int)/10^30)
theorem v23_mb_checked : Scalar.distance (sourceCoefficient 0 24 3 1) v23_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v23_mg : Scalar.QComplex := ((-93083798349411073153959 : Int)/10^30,(-629262451680313455159 : Int)/10^30)
theorem v23_mg_checked : Scalar.distance (sourceCoefficient 0 24 3 2) v23_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v23_upper : Scalar.QComplex := ((999982612076149122558929872180 : Int)/10^30,(5897079392534836666091646592 : Int)/10^30)
theorem v23_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 24 5) 1) 14) v23_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material23 : Material (0 : Basis) (24 : Basis) where
  plus := ![v23_pa,v23_pb,v23_pg]
  minus := ![(Primitive.Addresses.material23 1).one,v23_mb,v23_mg]
  upper := v23_upper
  lower := (Primitive.Addresses.material23 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v23_pa_checked.trans (by decide +kernel)
    · exact v23_pb_checked.trans (by decide +kernel)
    · exact v23_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 24 Primitive.Addresses.material23
    · exact v23_mb_checked.trans (by decide +kernel)
    · exact v23_mg_checked.trans (by decide +kernel)
  upper_error := v23_upper_checked
  lower_error := reuse_lower_error 0 24 Primitive.Addresses.material23

def v24_pa : Scalar.QComplex := ((999971119839794803262194756193 : Int)/10^30,(7599966206947238642518094124 : Int)/10^30)
theorem v24_pa_checked : Scalar.distance (sourceCoefficient 0 25 1 0) v24_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v24_pb : Scalar.QComplex := ((3279178823294981377545322 : Int)/10^30,(-431460355322075653014168685 : Int)/10^30)
theorem v24_pb_checked : Scalar.distance (sourceCoefficient 0 25 1 1) v24_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v24_pg : Scalar.QComplex := ((-93083234069727402979898 : Int)/10^30,(-707449864628715768617 : Int)/10^30)
theorem v24_pg_checked : Scalar.distance (sourceCoefficient 0 25 1 2) v24_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v24_mb : Scalar.QComplex := ((2906846747916932866014536 : Int)/10^30,(-431463024453302426074179920 : Int)/10^30)
theorem v24_mb_checked : Scalar.distance (sourceCoefficient 0 25 3 1) v24_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v24_mg : Scalar.QComplex := ((-93083809907956060331105 : Int)/10^30,(-627122962523860880445 : Int)/10^30)
theorem v24_mg_checked : Scalar.distance (sourceCoefficient 0 25 3 2) v24_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v24_upper : Scalar.QComplex := ((999982747352486303513849887458 : Int)/10^30,(5874095451518194426034982917 : Int)/10^30)
theorem v24_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 25 5) 1) 14) v24_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material24 : Material (0 : Basis) (25 : Basis) where
  plus := ![v24_pa,v24_pb,v24_pg]
  minus := ![(Primitive.Addresses.material24 1).one,v24_mb,v24_mg]
  upper := v24_upper
  lower := (Primitive.Addresses.material24 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v24_pa_checked.trans (by decide +kernel)
    · exact v24_pb_checked.trans (by decide +kernel)
    · exact v24_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 25 Primitive.Addresses.material24
    · exact v24_mb_checked.trans (by decide +kernel)
    · exact v24_mg_checked.trans (by decide +kernel)
  upper_error := v24_upper_checked
  lower_error := reuse_lower_error 0 25 Primitive.Addresses.material24

def v25_pa : Scalar.QComplex := ((999971175626455359305507159125 : Int)/10^30,(7592622487966272382073284644 : Int)/10^30)
theorem v25_pa_checked : Scalar.distance (sourceCoefficient 0 26 1 0) v25_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v25_pb : Scalar.QComplex := ((3276010143288599776405163 : Int)/10^30,(-431460370845589936099737881 : Int)/10^30)
theorem v25_pb_checked : Scalar.distance (sourceCoefficient 0 26 1 1) v25_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v25_pg : Scalar.QComplex := ((-93083238340727875646501 : Int)/10^30,(-706766260773244075947 : Int)/10^30)
theorem v25_pg_checked : Scalar.distance (sourceCoefficient 0 26 1 2) v25_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v25_mb : Scalar.QComplex := ((2903678055694301973907266 : Int)/10^30,(-431463037242382795588367207 : Int)/10^30)
theorem v25_mb_checked : Scalar.distance (sourceCoefficient 0 26 3 1) v25_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v25_mg : Scalar.QComplex := ((-93083813589035603811699 : Int)/10^30,(-626439355237245096215 : Int)/10^30)
theorem v25_mg_checked : Scalar.distance (sourceCoefficient 0 26 3 2) v25_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v25_upper : Scalar.QComplex := ((999982790464471027713411815441 : Int)/10^30,(5866751647192119740490887897 : Int)/10^30)
theorem v25_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 26 5) 1) 14) v25_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material25 : Material (0 : Basis) (26 : Basis) where
  plus := ![v25_pa,v25_pb,v25_pg]
  minus := ![(Primitive.Addresses.material25 1).one,v25_mb,v25_mg]
  upper := v25_upper
  lower := (Primitive.Addresses.material25 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v25_pa_checked.trans (by decide +kernel)
    · exact v25_pb_checked.trans (by decide +kernel)
    · exact v25_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 26 Primitive.Addresses.material25
    · exact v25_mb_checked.trans (by decide +kernel)
    · exact v25_mg_checked.trans (by decide +kernel)
  upper_error := v25_upper_checked
  lower_error := reuse_lower_error 0 26 Primitive.Addresses.material25

def v26_pa : Scalar.QComplex := ((999971213920281715694479234529 : Int)/10^30,(7587577399814980709287684915 : Int)/10^30)
theorem v26_pa_checked : Scalar.distance (sourceCoefficient 0 27 1 0) v26_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v26_pb : Scalar.QComplex := ((3273833280351293676234864 : Int)/10^30,(-431460381492165022980500325 : Int)/10^30)
theorem v26_pb_checked : Scalar.distance (sourceCoefficient 0 27 1 1) v26_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v26_pg : Scalar.QComplex := ((-93083241271483797035400 : Int)/10^30,(-706296629284110855487 : Int)/10^30)
theorem v26_pg_checked : Scalar.distance (sourceCoefficient 0 27 1 2) v26_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v26_mb : Scalar.QComplex := ((2901501184380026636810840 : Int)/10^30,(-431463046010419245634684072 : Int)/10^30)
theorem v26_mb_checked : Scalar.distance (sourceCoefficient 0 27 3 1) v26_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v26_mg : Scalar.QComplex := ((-93083816114519610241350 : Int)/10^30,(-625969721393866778567 : Int)/10^30)
theorem v26_mg_checked : Scalar.distance (sourceCoefficient 0 27 3 2) v26_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v26_upper : Scalar.QComplex := ((999982820050875887638739586858 : Int)/10^30,(5861706500463223929031831929 : Int)/10^30)
theorem v26_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 27 5) 1) 14) v26_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material26 : Material (0 : Basis) (27 : Basis) where
  plus := ![v26_pa,v26_pb,v26_pg]
  minus := ![(Primitive.Addresses.material26 1).one,v26_mb,v26_mg]
  upper := v26_upper
  lower := (Primitive.Addresses.material26 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v26_pa_checked.trans (by decide +kernel)
    · exact v26_pb_checked.trans (by decide +kernel)
    · exact v26_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 27 Primitive.Addresses.material26
    · exact v26_mb_checked.trans (by decide +kernel)
    · exact v26_mg_checked.trans (by decide +kernel)
  upper_error := v26_upper_checked
  lower_error := reuse_lower_error 0 27 Primitive.Addresses.material26

def v27_pa : Scalar.QComplex := ((999971265466796946057605978962 : Int)/10^30,(7580781010734282342634553391 : Int)/10^30)
theorem v27_pa_checked : Scalar.distance (sourceCoefficient 0 28 1 0) v27_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v27_pb : Scalar.QComplex := ((3270900763257035456197490 : Int)/10^30,(-431460395811332901468308677 : Int)/10^30)
theorem v27_pb_checked : Scalar.distance (sourceCoefficient 0 28 1 1) v27_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v27_pg : Scalar.QComplex := ((-93083245215222309057888 : Int)/10^30,(-705663974669990380646 : Int)/10^30)
theorem v27_pg_checked : Scalar.distance (sourceCoefficient 0 28 1 2) v27_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v27_mb : Scalar.QComplex := ((2898568656020881585863895 : Int)/10^30,(-431463057798951615764075238 : Int)/10^30)
theorem v27_mb_checked : Scalar.distance (sourceCoefficient 0 28 3 1) v27_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v27_mg : Scalar.QComplex := ((-93083819512304215549866 : Int)/10^30,(-625337063612043813821 : Int)/10^30)
theorem v27_mg_checked : Scalar.distance (sourceCoefficient 0 28 3 2) v27_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v27_upper : Scalar.QComplex := ((999982859867363355838199303903 : Int)/10^30,(5854910032540339713861748758 : Int)/10^30)
theorem v27_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 28 5) 1) 14) v27_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material27 : Material (0 : Basis) (28 : Basis) where
  plus := ![v27_pa,v27_pb,v27_pg]
  minus := ![(Primitive.Addresses.material27 1).one,v27_mb,v27_mg]
  upper := v27_upper
  lower := (Primitive.Addresses.material27 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v27_pa_checked.trans (by decide +kernel)
    · exact v27_pb_checked.trans (by decide +kernel)
    · exact v27_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 28 Primitive.Addresses.material27
    · exact v27_mb_checked.trans (by decide +kernel)
    · exact v27_mg_checked.trans (by decide +kernel)
  upper_error := v27_upper_checked
  lower_error := reuse_lower_error 0 28 Primitive.Addresses.material27

def v28_pa : Scalar.QComplex := ((999971369724215286163094969156 : Int)/10^30,(7567016048399538384485826596 : Int)/10^30)
theorem v28_pa_checked : Scalar.distance (sourceCoefficient 0 29 1 0) v28_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v28_pb : Scalar.QComplex := ((3264961434935224450914444 : Int)/10^30,(-431460424731020842596430499 : Int)/10^30)
theorem v28_pb_checked : Scalar.distance (sourceCoefficient 0 29 1 1) v28_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v28_pg : Scalar.QComplex := ((-93083253187242913991198 : Int)/10^30,(-704382637374270601094 : Int)/10^30)
theorem v28_pg_checked : Scalar.distance (sourceCoefficient 0 29 1 2) v28_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v28_mb : Scalar.QComplex := ((2892629304954165756705270 : Int)/10^30,(-431463081593255944465427448 : Int)/10^30)
theorem v28_mb_checked : Scalar.distance (sourceCoefficient 0 29 3 1) v28_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v28_mg : Scalar.QComplex := ((-93083826378585475218926 : Int)/10^30,(-624055719913929733895 : Int)/10^30)
theorem v28_mg_checked : Scalar.distance (sourceCoefficient 0 29 3 2) v28_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v28_upper : Scalar.QComplex := ((999982940367550174626262421478 : Int)/10^30,(5841144910768044311340698932 : Int)/10^30)
theorem v28_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 29 5) 1) 14) v28_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material28 : Material (0 : Basis) (29 : Basis) where
  plus := ![v28_pa,v28_pb,v28_pg]
  minus := ![(Primitive.Addresses.material28 1).one,v28_mb,v28_mg]
  upper := v28_upper
  lower := (Primitive.Addresses.material28 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v28_pa_checked.trans (by decide +kernel)
    · exact v28_pb_checked.trans (by decide +kernel)
    · exact v28_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 29 Primitive.Addresses.material28
    · exact v28_mb_checked.trans (by decide +kernel)
    · exact v28_mg_checked.trans (by decide +kernel)
  upper_error := v28_upper_checked
  lower_error := reuse_lower_error 0 29 Primitive.Addresses.material28

def v29_pa : Scalar.QComplex := ((999971409182418543165660435070 : Int)/10^30,(7561799900028014662084815220 : Int)/10^30)
theorem v29_pa_checked : Scalar.distance (sourceCoefficient 0 30 1 0) v29_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v29_pb : Scalar.QComplex := ((3262710762819247925554949 : Int)/10^30,(-431460435661477882567865015 : Int)/10^30)
theorem v29_pb_checked : Scalar.distance (sourceCoefficient 0 30 1 1) v29_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v29_pg : Scalar.QComplex := ((-93083256202814791072830 : Int)/10^30,(-703897082441807176213 : Int)/10^30)
theorem v29_pg_checked : Scalar.distance (sourceCoefficient 0 30 1 2) v29_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v29_mb : Scalar.QComplex := ((2890378624243725184936049 : Int)/10^30,(-431463090581480244949619917 : Int)/10^30)
theorem v29_mb_checked : Scalar.distance (sourceCoefficient 0 30 3 1) v29_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v29_mg : Scalar.QComplex := ((-93083828975144191331752 : Int)/10^30,(-623570162559957887721 : Int)/10^30)
theorem v29_mg_checked : Scalar.distance (sourceCoefficient 0 30 3 2) v29_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v29_upper : Scalar.QComplex := ((999982970823095779304005681383 : Int)/10^30,(5835928702064081655145077954 : Int)/10^30)
theorem v29_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 30 5) 1) 14) v29_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material29 : Material (0 : Basis) (30 : Basis) where
  plus := ![v29_pa,v29_pb,v29_pg]
  minus := ![(Primitive.Addresses.material29 1).one,v29_mb,v29_mg]
  upper := v29_upper
  lower := (Primitive.Addresses.material29 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v29_pa_checked.trans (by decide +kernel)
    · exact v29_pb_checked.trans (by decide +kernel)
    · exact v29_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 30 Primitive.Addresses.material29
    · exact v29_mb_checked.trans (by decide +kernel)
    · exact v29_mg_checked.trans (by decide +kernel)
  upper_error := v29_upper_checked
  lower_error := reuse_lower_error 0 30 Primitive.Addresses.material29

def v30_pa : Scalar.QComplex := ((999971493019565366501650455416 : Int)/10^30,(7550705147291443277630462216 : Int)/10^30)
theorem v30_pa_checked : Scalar.distance (sourceCoefficient 0 31 1 0) v30_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v30_pb : Scalar.QComplex := ((3257923581119478774189959 : Int)/10^30,(-431460458858511962473515858 : Int)/10^30)
theorem v30_pb_checked : Scalar.distance (sourceCoefficient 0 31 1 1) v30_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v30_pg : Scalar.QComplex := ((-93083262607111870031037 : Int)/10^30,(-702864306633238122954 : Int)/10^30)
theorem v30_pg_checked : Scalar.distance (sourceCoefficient 0 31 1 2) v30_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v30_mb : Scalar.QComplex := ((2885591424308446910080223 : Int)/10^30,(-431463109647383487298610517 : Int)/10^30)
theorem v30_mb_checked : Scalar.distance (sourceCoefficient 0 31 3 1) v30_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v30_mg : Scalar.QComplex := ((-93083834488199877378091 : Int)/10^30,(-622537381609318527871 : Int)/10^30)
theorem v30_mg_checked : Scalar.distance (sourceCoefficient 0 31 3 2) v30_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v30_upper : Scalar.QComplex := ((999983035511581021841647748447 : Int)/10^30,(5824833821156531420076696805 : Int)/10^30)
theorem v30_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 31 5) 1) 14) v30_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material30 : Material (0 : Basis) (31 : Basis) where
  plus := ![v30_pa,v30_pb,v30_pg]
  minus := ![(Primitive.Addresses.material30 1).one,v30_mb,v30_mg]
  upper := v30_upper
  lower := (Primitive.Addresses.material30 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v30_pa_checked.trans (by decide +kernel)
    · exact v30_pb_checked.trans (by decide +kernel)
    · exact v30_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 31 Primitive.Addresses.material30
    · exact v30_mb_checked.trans (by decide +kernel)
    · exact v30_mg_checked.trans (by decide +kernel)
  upper_error := v30_upper_checked
  lower_error := reuse_lower_error 0 31 Primitive.Addresses.material30

def v31_pa : Scalar.QComplex := ((999971529071008025482908482811 : Int)/10^30,(7545929193290337794510641783 : Int)/10^30)
theorem v31_pa_checked : Scalar.distance (sourceCoefficient 0 32 1 0) v31_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v31_pb : Scalar.QComplex := ((3255862844876985445637018 : Int)/10^30,(-431460468822325465982658889 : Int)/10^30)
theorem v31_pb_checked : Scalar.distance (sourceCoefficient 0 32 1 1) v31_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v31_pg : Scalar.QComplex := ((-93083265359851025934424 : Int)/10^30,(-702419728027890340818 : Int)/10^30)
theorem v31_pg_checked : Scalar.distance (sourceCoefficient 0 32 1 2) v31_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v31_mb : Scalar.QComplex := ((2883530680234937564879726 : Int)/10^30,(-431463117832870715667889118 : Int)/10^30)
theorem v31_mb_checked : Scalar.distance (sourceCoefficient 0 32 3 1) v31_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v31_mg : Scalar.QComplex := ((-93083836857286694972842 : Int)/10^30,(-622092800794017765977 : Int)/10^30)
theorem v31_mg_checked : Scalar.distance (sourceCoefficient 0 32 3 2) v31_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v31_upper : Scalar.QComplex := ((999983063320106651688353004507 : Int)/10^30,(5820057812047128930564958045 : Int)/10^30)
theorem v31_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 32 5) 1) 14) v31_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material31 : Material (0 : Basis) (32 : Basis) where
  plus := ![v31_pa,v31_pb,v31_pg]
  minus := ![(Primitive.Addresses.material31 1).one,v31_mb,v31_mg]
  upper := v31_upper
  lower := (Primitive.Addresses.material31 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v31_pa_checked.trans (by decide +kernel)
    · exact v31_pb_checked.trans (by decide +kernel)
    · exact v31_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 32 Primitive.Addresses.material31
    · exact v31_mb_checked.trans (by decide +kernel)
    · exact v31_mg_checked.trans (by decide +kernel)
  upper_error := v31_upper_checked
  lower_error := reuse_lower_error 0 32 Primitive.Addresses.material31

def v32_pa : Scalar.QComplex := ((999971579275448737148636981466 : Int)/10^30,(7539273265039653937787830186 : Int)/10^30)
theorem v32_pa_checked : Scalar.distance (sourceCoefficient 0 33 1 0) v32_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v32_pb : Scalar.QComplex := ((3252990934397528397386842 : Int)/10^30,(-431460482686338206754158894 : Int)/10^30)
theorem v32_pb_checked : Scalar.distance (sourceCoefficient 0 33 1 1) v32_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v32_pg : Scalar.QComplex := ((-93083269192027780442657 : Int)/10^30,(-701800148510655171087 : Int)/10^30)
theorem v32_pg_checked : Scalar.distance (sourceCoefficient 0 33 1 2) v32_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v32_mb : Scalar.QComplex := ((2880658758860805457593118 : Int)/10^30,(-431463129218548896508840213 : Int)/10^30)
theorem v32_mb_checked : Scalar.distance (sourceCoefficient 0 33 3 1) v32_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v32_mg : Scalar.QComplex := ((-93083840154792804038159 : Int)/10^30,(-621473218200484422388 : Int)/10^30)
theorem v32_mg_checked : Scalar.distance (sourceCoefficient 0 33 3 2) v32_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v32_upper : Scalar.QComplex := ((999983102036944250150843153414 : Int)/10^30,(5813401807061358185929163598 : Int)/10^30)
theorem v32_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 33 5) 1) 14) v32_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material32 : Material (0 : Basis) (33 : Basis) where
  plus := ![v32_pa,v32_pb,v32_pg]
  minus := ![(Primitive.Addresses.material32 1).one,v32_mb,v32_mg]
  upper := v32_upper
  lower := (Primitive.Addresses.material32 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v32_pa_checked.trans (by decide +kernel)
    · exact v32_pb_checked.trans (by decide +kernel)
    · exact v32_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 33 Primitive.Addresses.material32
    · exact v32_mb_checked.trans (by decide +kernel)
    · exact v32_mg_checked.trans (by decide +kernel)
  upper_error := v32_upper_checked
  lower_error := reuse_lower_error 0 33 Primitive.Addresses.material32

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
