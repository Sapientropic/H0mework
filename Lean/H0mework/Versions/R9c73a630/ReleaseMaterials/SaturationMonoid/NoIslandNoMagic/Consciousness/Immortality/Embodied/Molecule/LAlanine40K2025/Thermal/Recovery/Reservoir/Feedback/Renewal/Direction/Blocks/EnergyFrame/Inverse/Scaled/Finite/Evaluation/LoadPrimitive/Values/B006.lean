import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B004

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v97_pa : Scalar.QComplex := ((999905873599733062568544809603 : Int)/10^30,(13720201921059604113694069103 : Int)/10^30)
theorem v97_pa_checked : Scalar.distance (sourceCoefficient 1 2 1 0) v97_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v97_pb : Scalar.QComplex := ((5919954952186821426987056 : Int)/10^30,(-431436633527349546478505716 : Int)/10^30)
theorem v97_pb_checked : Scalar.distance (sourceCoefficient 1 2 1 1) v97_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v97_pg : Scalar.QComplex := ((-93077638445084013635785 : Int)/10^30,(-1277164208671444961867 : Int)/10^30)
theorem v97_pg_checked : Scalar.distance (sourceCoefficient 1 2 1 2) v97_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v97_mb : Scalar.QComplex := ((5547642364367589353731522 : Int)/10^30,(-431441581538272119784412511 : Int)/10^30)
theorem v97_mb_checked : Scalar.distance (sourceCoefficient 1 2 3 1) v97_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v97_mg : Scalar.QComplex := ((-93078705923216105100183 : Int)/10^30,(-1196841923207952221196 : Int)/10^30)
theorem v97_mg_checked : Scalar.distance (sourceCoefficient 1 2 3 2) v97_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v97_upper : Scalar.QComplex := ((999928064181220284156492212685 : Int)/10^30,(11994434659349651019588910503 : Int)/10^30)
theorem v97_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 2 5) 1) 14) v97_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material97 : Material (1 : Basis) (2 : Basis) where
  plus := ![v97_pa,v97_pb,v97_pg]
  minus := ![(Primitive.Addresses.material97 1).one,v97_mb,v97_mg]
  upper := v97_upper
  lower := (Primitive.Addresses.material97 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v97_pa_checked.trans (by decide +kernel)
    · exact v97_pb_checked.trans (by decide +kernel)
    · exact v97_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 2 Primitive.Addresses.material97
    · exact v97_mb_checked.trans (by decide +kernel)
    · exact v97_mg_checked.trans (by decide +kernel)
  upper_error := v97_upper_checked
  lower_error := reuse_lower_error 1 2 Primitive.Addresses.material97

def v98_pa : Scalar.QComplex := ((999929013368687045321241728552 : Int)/10^30,(11915041901902158067745665096 : Int)/10^30)
theorem v98_pa_checked : Scalar.distance (sourceCoefficient 1 3 1 0) v98_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v98_pb : Scalar.QComplex := ((5141060644607913756524211 : Int)/10^30,(-431445876594919836452069836 : Int)/10^30)
theorem v98_pb_checked : Scalar.distance (sourceCoefficient 1 3 1 1) v98_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v98_pg : Scalar.QComplex := ((-93079712488317971217439 : Int)/10^30,(-1109127407733686097965 : Int)/10^30)
theorem v98_pg_checked : Scalar.distance (sourceCoefficient 1 3 1 2) v98_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v98_mb : Scalar.QComplex := ((4768740370455608772912855 : Int)/10^30,(-431450152451693450054108916 : Int)/10^30)
theorem v98_mb_checked : Scalar.distance (sourceCoefficient 1 3 3 1) v98_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v98_mg : Scalar.QComplex := ((-93080634957486688884762 : Int)/10^30,(-1028803395032074541876 : Int)/10^30)
theorem v98_mg_checked : Scalar.distance (sourceCoefficient 1 3 3 2) v98_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v98_upper : Scalar.QComplex := ((999948088373280071181438517147 : Int)/10^30,(10189237391624013384217482545 : Int)/10^30)
theorem v98_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 3 5) 1) 14) v98_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material98 : Material (1 : Basis) (3 : Basis) where
  plus := ![v98_pa,v98_pb,v98_pg]
  minus := ![(Primitive.Addresses.material98 1).one,v98_mb,v98_mg]
  upper := v98_upper
  lower := (Primitive.Addresses.material98 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v98_pa_checked.trans (by decide +kernel)
    · exact v98_pb_checked.trans (by decide +kernel)
    · exact v98_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 3 Primitive.Addresses.material98
    · exact v98_mb_checked.trans (by decide +kernel)
    · exact v98_mg_checked.trans (by decide +kernel)
  upper_error := v98_upper_checked
  lower_error := reuse_lower_error 1 3 Primitive.Addresses.material98

def v99_pa : Scalar.QComplex := ((999929077069706574580804605657 : Int)/10^30,(11909694812412677113929754255 : Int)/10^30)
theorem v99_pa_checked : Scalar.distance (sourceCoefficient 1 4 1 0) v99_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v99_pb : Scalar.QComplex := ((5138753466676862431193205 : Int)/10^30,(-431445901188630924973271247 : Int)/10^30)
theorem v99_pb_checked : Scalar.distance (sourceCoefficient 1 4 1 1) v99_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v99_pg : Scalar.QComplex := ((-93079718106076568136258 : Int)/10^30,(-1108629663133094050774 : Int)/10^30)
theorem v99_pg_checked : Scalar.distance (sourceCoefficient 1 4 1 2) v99_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v99_mb : Scalar.QComplex := ((4766433172160360224788079 : Int)/10^30,(-431450175054404738152030893 : Int)/10^30)
theorem v99_mb_checked : Scalar.distance (sourceCoefficient 1 4 3 1) v99_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v99_mg : Scalar.QComplex := ((-93080640145712021329005 : Int)/10^30,(-1028305645768942902852 : Int)/10^30)
theorem v99_mg_checked : Scalar.distance (sourceCoefficient 1 4 3 2) v99_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v99_upper : Scalar.QComplex := ((999948142845613350580349802370 : Int)/10^30,(10183890200156213315576779178 : Int)/10^30)
theorem v99_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 4 5) 1) 14) v99_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material99 : Material (1 : Basis) (4 : Basis) where
  plus := ![v99_pa,v99_pb,v99_pg]
  minus := ![(Primitive.Addresses.material99 1).one,v99_mb,v99_mg]
  upper := v99_upper
  lower := (Primitive.Addresses.material99 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v99_pa_checked.trans (by decide +kernel)
    · exact v99_pb_checked.trans (by decide +kernel)
    · exact v99_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 4 Primitive.Addresses.material99
    · exact v99_mb_checked.trans (by decide +kernel)
    · exact v99_mg_checked.trans (by decide +kernel)
  upper_error := v99_upper_checked
  lower_error := reuse_lower_error 1 4 Primitive.Addresses.material99

def v100_pa : Scalar.QComplex := ((999929372803986538339305076785 : Int)/10^30,(11884839242754047342400766916 : Int)/10^30)
theorem v100_pa_checked : Scalar.distance (sourceCoefficient 1 5 1 0) v100_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v100_pb : Scalar.QComplex := ((5128028711994350680491577 : Int)/10^30,(-431446015294786877095412039 : Int)/10^30)
theorem v100_pb_checked : Scalar.distance (sourceCoefficient 1 5 1 1) v100_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v100_pg : Scalar.QComplex := ((-93079744179060948162695 : Int)/10^30,(-1106315932317015734617 : Int)/10^30)
theorem v100_pg_checked : Scalar.distance (sourceCoefficient 1 5 1 2) v100_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v100_mb : Scalar.QComplex := ((4755708323002691351696689 : Int)/10^30,(-431450279905537937349929645 : Int)/10^30)
theorem v100_mb_checked : Scalar.distance (sourceCoefficient 1 5 3 1) v100_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v100_mg : Scalar.QComplex := ((-93080664222041205483803 : Int)/10^30,(-1025991893314561075906 : Int)/10^30)
theorem v100_mg_checked : Scalar.distance (sourceCoefficient 1 5 3 2) v100_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v100_upper : Scalar.QComplex := ((999948395680994501738525013811 : Int)/10^30,(10159034157106496397120185690 : Int)/10^30)
theorem v100_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 5 5) 1) 14) v100_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material100 : Material (1 : Basis) (5 : Basis) where
  plus := ![v100_pa,v100_pb,v100_pg]
  minus := ![(Primitive.Addresses.material100 1).one,v100_mb,v100_mg]
  upper := v100_upper
  lower := (Primitive.Addresses.material100 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v100_pa_checked.trans (by decide +kernel)
    · exact v100_pb_checked.trans (by decide +kernel)
    · exact v100_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 5 Primitive.Addresses.material100
    · exact v100_mb_checked.trans (by decide +kernel)
    · exact v100_mg_checked.trans (by decide +kernel)
  upper_error := v100_upper_checked
  lower_error := reuse_lower_error 1 5 Primitive.Addresses.material100

def v101_pa : Scalar.QComplex := ((999967594423727058587951465963 : Int)/10^30,(8050472186431628351536292233 : Int)/10^30)
theorem v101_pa_checked : Scalar.distance (sourceCoefficient 1 6 1 0) v101_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v101_pb : Scalar.QComplex := ((3473564146306483568555103 : Int)/10^30,(-431459360770515105601200206 : Int)/10^30)
theorem v101_pb_checked : Scalar.distance (sourceCoefficient 1 6 1 1) v101_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v101_pg : Scalar.QComplex := ((-93082962703980531491966 : Int)/10^30,(-749386086567033995105 : Int)/10^30)
theorem v101_pg_checked : Scalar.distance (sourceCoefficient 1 6 1 2) v101_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v101_mb : Scalar.QComplex := ((3101232856803099264631834 : Int)/10^30,(-431462197647891164631487355 : Int)/10^30)
theorem v101_mb_checked : Scalar.distance (sourceCoefficient 1 6 3 1) v101_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v101_mg : Scalar.QComplex := ((-93083574731381026158514 : Int)/10^30,(-669059403023824789825 : Int)/10^30)
theorem v101_mg_checked : Scalar.distance (sourceCoefficient 1 6 3 2) v101_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v101_upper : Scalar.QComplex := ((999979999474120258801527992301 : Int)/10^30,(6324606844575157522806765310 : Int)/10^30)
theorem v101_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 6 5) 1) 14) v101_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material101 : Material (1 : Basis) (6 : Basis) where
  plus := ![v101_pa,v101_pb,v101_pg]
  minus := ![(Primitive.Addresses.material101 1).one,v101_mb,v101_mg]
  upper := v101_upper
  lower := (Primitive.Addresses.material101 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v101_pa_checked.trans (by decide +kernel)
    · exact v101_pb_checked.trans (by decide +kernel)
    · exact v101_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 6 Primitive.Addresses.material101
    · exact v101_mb_checked.trans (by decide +kernel)
    · exact v101_mg_checked.trans (by decide +kernel)
  upper_error := v101_upper_checked
  lower_error := reuse_lower_error 1 6 Primitive.Addresses.material101

def v102_pa : Scalar.QComplex := ((999968071322210117879931685967 : Int)/10^30,(7991015964149917153189046278 : Int)/10^30)
theorem v102_pa_checked : Scalar.distance (sourceCoefficient 1 7 1 0) v102_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v102_pb : Scalar.QComplex := ((3447909848414952042844195 : Int)/10^30,(-431459501104767191078982169 : Int)/10^30)
theorem v102_pb_checked : Scalar.distance (sourceCoefficient 1 7 1 1) v102_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v102_pg : Scalar.QComplex := ((-93083000038124930790793 : Int)/10^30,(-743851489490155124001 : Int)/10^30)
theorem v102_pg_checked : Scalar.distance (sourceCoefficient 1 7 1 2) v102_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v102_mb : Scalar.QComplex := ((3075578447361696173594004 : Int)/10^30,(-431462315843587343547498928 : Int)/10^30)
theorem v102_mb_checked : Scalar.distance (sourceCoefficient 1 7 3 1) v102_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v102_mg : Scalar.QComplex := ((-93083607289403515901702 : Int)/10^30,(-663524775790044204875 : Int)/10^30)
theorem v102_mg_checked : Scalar.distance (sourceCoefficient 1 7 3 2) v102_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v102_upper : Scalar.QComplex := ((999980373755847201941031735533 : Int)/10^30,(6265149887762987326670749994 : Int)/10^30)
theorem v102_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 7 5) 1) 14) v102_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material102 : Material (1 : Basis) (7 : Basis) where
  plus := ![v102_pa,v102_pb,v102_pg]
  minus := ![(Primitive.Addresses.material102 1).one,v102_mb,v102_mg]
  upper := v102_upper
  lower := (Primitive.Addresses.material102 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v102_pa_checked.trans (by decide +kernel)
    · exact v102_pb_checked.trans (by decide +kernel)
    · exact v102_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 7 Primitive.Addresses.material102
    · exact v102_mb_checked.trans (by decide +kernel)
    · exact v102_mg_checked.trans (by decide +kernel)
  upper_error := v102_upper_checked
  lower_error := reuse_lower_error 1 7 Primitive.Addresses.material102

def v103_pa : Scalar.QComplex := ((999968376899505130473628643615 : Int)/10^30,(7952685142092206841792038892 : Int)/10^30)
theorem v103_pa_checked : Scalar.distance (sourceCoefficient 1 8 1 0) v103_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v103_pb : Scalar.QComplex := ((3431370785354187801474801 : Int)/10^30,(-431459590498550113531255149 : Int)/10^30)
theorem v103_pb_checked : Scalar.distance (sourceCoefficient 1 8 1 1) v103_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v103_pg : Scalar.QComplex := ((-93083023903518056322596 : Int)/10^30,(-740283391234597474195 : Int)/10^30)
theorem v103_pg_checked : Scalar.distance (sourceCoefficient 1 8 1 2) v103_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v103_mb : Scalar.QComplex := ((3059039313316372466718806 : Int)/10^30,(-431462390964870450917927206 : Int)/10^30)
theorem v103_mb_checked : Scalar.distance (sourceCoefficient 1 8 3 1) v103_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v103_mg : Scalar.QComplex := ((-93083628075679661890613 : Int)/10^30,(-659956658268293195830 : Int)/10^30)
theorem v103_mg_checked : Scalar.distance (sourceCoefficient 1 8 3 2) v103_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v103_upper : Scalar.QComplex := ((999980613177165566454987490703 : Int)/10^30,(6226818595395844379496464887 : Int)/10^30)
theorem v103_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 8 5) 1) 14) v103_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material103 : Material (1 : Basis) (8 : Basis) where
  plus := ![v103_pa,v103_pb,v103_pg]
  minus := ![(Primitive.Addresses.material103 1).one,v103_mb,v103_mg]
  upper := v103_upper
  lower := (Primitive.Addresses.material103 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v103_pa_checked.trans (by decide +kernel)
    · exact v103_pb_checked.trans (by decide +kernel)
    · exact v103_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 8 Primitive.Addresses.material103
    · exact v103_mb_checked.trans (by decide +kernel)
    · exact v103_mg_checked.trans (by decide +kernel)
  upper_error := v103_upper_checked
  lower_error := reuse_lower_error 1 8 Primitive.Addresses.material103

def v104_pa : Scalar.QComplex := ((999968544946376437089613883777 : Int)/10^30,(7931526828217084178411256034 : Int)/10^30)
theorem v104_pa_checked : Scalar.distance (sourceCoefficient 1 9 1 0) v104_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v104_pb : Scalar.QComplex := ((3422241352622671247835734 : Int)/10^30,(-431459639481124713645155724 : Int)/10^30)
theorem v104_pb_checked : Scalar.distance (sourceCoefficient 1 9 1 1) v104_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v104_pg : Scalar.QComplex := ((-93083037008674888322906 : Int)/10^30,(-738313828987310413981 : Int)/10^30)
theorem v104_pg_checked : Scalar.distance (sourceCoefficient 1 9 1 2) v104_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v104_mb : Scalar.QComplex := ((3049909841714405168078705 : Int)/10^30,(-431462432069137539668620922 : Int)/10^30)
theorem v104_mb_checked : Scalar.distance (sourceCoefficient 1 9 3 1) v104_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v104_mg : Scalar.QComplex := ((-93083639481188100624069 : Int)/10^30,(-657987085445204062061 : Int)/10^30)
theorem v104_mg_checked : Scalar.distance (sourceCoefficient 1 9 3 2) v104_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v104_upper : Scalar.QComplex := ((999980744706456305775312599598 : Int)/10^30,(6205660022999890020828786342 : Int)/10^30)
theorem v104_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 9 5) 1) 14) v104_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material104 : Material (1 : Basis) (9 : Basis) where
  plus := ![v104_pa,v104_pb,v104_pg]
  minus := ![(Primitive.Addresses.material104 1).one,v104_mb,v104_mg]
  upper := v104_upper
  lower := (Primitive.Addresses.material104 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v104_pa_checked.trans (by decide +kernel)
    · exact v104_pb_checked.trans (by decide +kernel)
    · exact v104_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 9 Primitive.Addresses.material104
    · exact v104_mb_checked.trans (by decide +kernel)
    · exact v104_mg_checked.trans (by decide +kernel)
  upper_error := v104_upper_checked
  lower_error := reuse_lower_error 1 9 Primitive.Addresses.material104

def v105_pa : Scalar.QComplex := ((999968876202420407324239858463 : Int)/10^30,(7889653127255315276062571415 : Int)/10^30)
theorem v105_pa_checked : Scalar.distance (sourceCoefficient 1 10 1 0) v105_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v105_pb : Scalar.QComplex := ((3404173603557382227937122 : Int)/10^30,(-431459735661590519236378461 : Int)/10^30)
theorem v105_pb_checked : Scalar.distance (sourceCoefficient 1 10 1 1) v105_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v105_pg : Scalar.QComplex := ((-93083062801313786448577 : Int)/10^30,(-734415935337798903715 : Int)/10^30)
theorem v105_pg_checked : Scalar.distance (sourceCoefficient 1 10 1 2) v105_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v105_mb : Scalar.QComplex := ((3031842016377154679262120 : Int)/10^30,(-431462512657913830742742599 : Int)/10^30)
theorem v105_mb_checked : Scalar.distance (sourceCoefficient 1 10 3 1) v105_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v105_mg : Scalar.QComplex := ((-93083661910110730056144 : Int)/10^30,(-654089170989170788298 : Int)/10^30)
theorem v105_mg_checked : Scalar.distance (sourceCoefficient 1 10 3 2) v105_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v105_upper : Scalar.QComplex := ((999981003691797801508413602511 : Int)/10^30,(6163785812686199291526955678 : Int)/10^30)
theorem v105_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 10 5) 1) 14) v105_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material105 : Material (1 : Basis) (10 : Basis) where
  plus := ![v105_pa,v105_pb,v105_pg]
  minus := ![(Primitive.Addresses.material105 1).one,v105_mb,v105_mg]
  upper := v105_upper
  lower := (Primitive.Addresses.material105 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v105_pa_checked.trans (by decide +kernel)
    · exact v105_pb_checked.trans (by decide +kernel)
    · exact v105_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 10 Primitive.Addresses.material105
    · exact v105_mb_checked.trans (by decide +kernel)
    · exact v105_mg_checked.trans (by decide +kernel)
  upper_error := v105_upper_checked
  lower_error := reuse_lower_error 1 10 Primitive.Addresses.material105

def v106_pa : Scalar.QComplex := ((999968947271285177455949422936 : Int)/10^30,(7880640402764514653462888273 : Int)/10^30)
theorem v106_pa_checked : Scalar.distance (sourceCoefficient 1 11 1 0) v106_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v106_pb : Scalar.QComplex := ((3400284775242779257830255 : Int)/10^30,(-431459756231146352519515072 : Int)/10^30)
theorem v106_pb_checked : Scalar.distance (sourceCoefficient 1 11 1 1) v106_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v106_pg : Scalar.QComplex := ((-93083068327910387394728 : Int)/10^30,(-733576968644819322322 : Int)/10^30)
theorem v106_pg_checked : Scalar.distance (sourceCoefficient 1 11 1 2) v106_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v106_mb : Scalar.QComplex := ((3027953171759939953196986 : Int)/10^30,(-431462529871578315863356630 : Int)/10^30)
theorem v106_mb_checked : Scalar.distance (sourceCoefficient 1 11 3 1) v106_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v106_mg : Scalar.QComplex := ((-93083666712714802813606 : Int)/10^30,(-653250199839372891428 : Int)/10^30)
theorem v106_mg_checked : Scalar.distance (sourceCoefficient 1 11 3 2) v106_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v106_upper : Scalar.QComplex := ((999981059205411879771354911004 : Int)/10^30,(6154772978960379812786798986 : Int)/10^30)
theorem v106_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 11 5) 1) 14) v106_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material106 : Material (1 : Basis) (11 : Basis) where
  plus := ![v106_pa,v106_pb,v106_pg]
  minus := ![(Primitive.Addresses.material106 1).one,v106_mb,v106_mg]
  upper := v106_upper
  lower := (Primitive.Addresses.material106 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v106_pa_checked.trans (by decide +kernel)
    · exact v106_pb_checked.trans (by decide +kernel)
    · exact v106_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 11 Primitive.Addresses.material106
    · exact v106_mb_checked.trans (by decide +kernel)
    · exact v106_mg_checked.trans (by decide +kernel)
  upper_error := v106_upper_checked
  lower_error := reuse_lower_error 1 11 Primitive.Addresses.material106

def v107_pa : Scalar.QComplex := ((999968986042154786271207761658 : Int)/10^30,(7875719257619981523098162472 : Int)/10^30)
theorem v107_pa_checked : Scalar.distance (sourceCoefficient 1 12 1 0) v107_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v107_pb : Scalar.QComplex := ((3398161389771975945805001 : Int)/10^30,(-431459767442848711115392821 : Int)/10^30)
theorem v107_pb_checked : Scalar.distance (sourceCoefficient 1 12 1 1) v107_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v107_pg : Scalar.QComplex := ((-93083071341829546918072 : Int)/10^30,(-733118874443129086361 : Int)/10^30)
theorem v107_pg_checked : Scalar.distance (sourceCoefficient 1 12 1 2) v107_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v107_mb : Scalar.QComplex := ((3025829777404575916322996 : Int)/10^30,(-431462539250890472258301880 : Int)/10^30)
theorem v107_mb_checked : Scalar.distance (sourceCoefficient 1 12 3 1) v107_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v107_mg : Scalar.QComplex := ((-93083669331318175855386 : Int)/10^30,(-652792103207375569907 : Int)/10^30)
theorem v107_mg_checked : Scalar.distance (sourceCoefficient 1 12 3 2) v107_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v107_upper : Scalar.QComplex := ((999981089482773667266586454762 : Int)/10^30,(6149851774230310617888110159 : Int)/10^30)
theorem v107_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 12 5) 1) 14) v107_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material107 : Material (1 : Basis) (12 : Basis) where
  plus := ![v107_pa,v107_pb,v107_pg]
  minus := ![(Primitive.Addresses.material107 1).one,v107_mb,v107_mg]
  upper := v107_upper
  lower := (Primitive.Addresses.material107 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v107_pa_checked.trans (by decide +kernel)
    · exact v107_pb_checked.trans (by decide +kernel)
    · exact v107_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 12 Primitive.Addresses.material107
    · exact v107_mb_checked.trans (by decide +kernel)
    · exact v107_mg_checked.trans (by decide +kernel)
  upper_error := v107_upper_checked
  lower_error := reuse_lower_error 1 12 Primitive.Addresses.material107

def v108_pa : Scalar.QComplex := ((999969390434418733294999781283 : Int)/10^30,(7824205660450671981244826919 : Int)/10^30)
theorem v108_pa_checked : Scalar.distance (sourceCoefficient 1 13 1 0) v108_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v108_pb : Scalar.QComplex := ((3375934202282844067719982 : Int)/10^30,(-431459883968468483351486248 : Int)/10^30)
theorem v108_pb_checked : Scalar.distance (sourceCoefficient 1 13 1 1) v108_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v108_pg : Scalar.QComplex := ((-93083102733079888974791 : Int)/10^30,(-728323632966482756853 : Int)/10^30)
theorem v108_pg_checked : Scalar.distance (sourceCoefficient 1 13 1 2) v108_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v108_mb : Scalar.QComplex := ((3003602497635280028748634 : Int)/10^30,(-431462636595405128922705640 : Int)/10^30)
theorem v108_mb_checked : Scalar.distance (sourceCoefficient 1 13 3 1) v108_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v108_mg : Scalar.QComplex := ((-93083696584479404828107 : Int)/10^30,(-647996836426981559754 : Int)/10^30)
theorem v108_mg_checked : Scalar.distance (sourceCoefficient 1 13 3 2) v108_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v108_upper : Scalar.QComplex := ((999981404966639882317775365586 : Int)/10^30,(6098337555840091454568858122 : Int)/10^30)
theorem v108_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 13 5) 1) 14) v108_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material108 : Material (1 : Basis) (13 : Basis) where
  plus := ![v108_pa,v108_pb,v108_pg]
  minus := ![(Primitive.Addresses.material108 1).one,v108_mb,v108_mg]
  upper := v108_upper
  lower := (Primitive.Addresses.material108 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v108_pa_checked.trans (by decide +kernel)
    · exact v108_pb_checked.trans (by decide +kernel)
    · exact v108_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 13 Primitive.Addresses.material108
    · exact v108_mb_checked.trans (by decide +kernel)
    · exact v108_mg_checked.trans (by decide +kernel)
  upper_error := v108_upper_checked
  lower_error := reuse_lower_error 1 13 Primitive.Addresses.material108

def v109_pa : Scalar.QComplex := ((999969517916805954873490654461 : Int)/10^30,(7807895826065714379213920311 : Int)/10^30)
theorem v109_pa_checked : Scalar.distance (sourceCoefficient 1 14 1 0) v109_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v109_pb : Scalar.QComplex := ((3368896803720296324378509 : Int)/10^30,(-431459920543681194441755165 : Int)/10^30)
theorem v109_pb_checked : Scalar.distance (sourceCoefficient 1 14 1 1) v109_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v109_pg : Scalar.QComplex := ((-93083112611861678706584 : Int)/10^30,(-726805400982058274651 : Int)/10^30)
theorem v109_pg_checked : Scalar.distance (sourceCoefficient 1 14 1 2) v109_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v109_mb : Scalar.QComplex := ((2996565070130316112006051 : Int)/10^30,(-431462667097646214576431068 : Int)/10^30)
theorem v109_mb_checked : Scalar.distance (sourceCoefficient 1 14 3 1) v109_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v109_mg : Scalar.QComplex := ((-93083705153091692309874 : Int)/10^30,(-646478596482920471259 : Int)/10^30)
theorem v109_mg_checked : Scalar.distance (sourceCoefficient 1 14 3 2) v109_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v109_upper : Scalar.QComplex := ((999981504299542702036084372175 : Int)/10^30,(6082027525723681048584240509 : Int)/10^30)
theorem v109_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 14 5) 1) 14) v109_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material109 : Material (1 : Basis) (14 : Basis) where
  plus := ![v109_pa,v109_pb,v109_pg]
  minus := ![(Primitive.Addresses.material109 1).one,v109_mb,v109_mg]
  upper := v109_upper
  lower := (Primitive.Addresses.material109 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v109_pa_checked.trans (by decide +kernel)
    · exact v109_pb_checked.trans (by decide +kernel)
    · exact v109_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 14 Primitive.Addresses.material109
    · exact v109_mb_checked.trans (by decide +kernel)
    · exact v109_mg_checked.trans (by decide +kernel)
  upper_error := v109_upper_checked
  lower_error := reuse_lower_error 1 14 Primitive.Addresses.material109

def v110_pa : Scalar.QComplex := ((999969722748834735246589065279 : Int)/10^30,(7781618444680475484357873984 : Int)/10^30)
theorem v110_pa_checked : Scalar.distance (sourceCoefficient 1 15 1 0) v110_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v110_pb : Scalar.QComplex := ((3357558589535431445633904 : Int)/10^30,(-431459979149437213272020590 : Int)/10^30)
theorem v110_pb_checked : Scalar.distance (sourceCoefficient 1 15 1 1) v110_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v110_pg : Scalar.QComplex := ((-93083128467163083171458 : Int)/10^30,(-724359320977733626763 : Int)/10^30)
theorem v110_pg_checked : Scalar.distance (sourceCoefficient 1 15 1 2) v110_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v110_mb : Scalar.QComplex := ((2985226809593058617291125 : Int)/10^30,(-431462715919012224477435927 : Int)/10^30)
theorem v110_mb_checked : Scalar.distance (sourceCoefficient 1 15 3 1) v110_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v110_mg : Scalar.QComplex := ((-93083718897530316743031 : Int)/10^30,(-644032503706972184574 : Int)/10^30)
theorem v110_mg_checked : Scalar.distance (sourceCoefficient 1 15 3 2) v110_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v110_upper : Scalar.QComplex := ((999981663778890003658776369226 : Int)/10^30,(6055749829954015510561769535 : Int)/10^30)
theorem v110_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 15 5) 1) 14) v110_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material110 : Material (1 : Basis) (15 : Basis) where
  plus := ![v110_pa,v110_pb,v110_pg]
  minus := ![(Primitive.Addresses.material110 1).one,v110_mb,v110_mg]
  upper := v110_upper
  lower := (Primitive.Addresses.material110 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v110_pa_checked.trans (by decide +kernel)
    · exact v110_pb_checked.trans (by decide +kernel)
    · exact v110_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 15 Primitive.Addresses.material110
    · exact v110_mb_checked.trans (by decide +kernel)
    · exact v110_mg_checked.trans (by decide +kernel)
  upper_error := v110_upper_checked
  lower_error := reuse_lower_error 1 15 Primitive.Addresses.material110

def v111_pa : Scalar.QComplex := ((999969748675198074961639229426 : Int)/10^30,(7778286087641531661058854414 : Int)/10^30)
theorem v111_pa_checked : Scalar.distance (sourceCoefficient 1 16 1 0) v111_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v111_pb : Scalar.QComplex := ((3356120737878659588638595 : Int)/10^30,(-431459986553121018307612110 : Int)/10^30)
theorem v111_pb_checked : Scalar.distance (sourceCoefficient 1 16 1 1) v111_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v111_pg : Scalar.QComplex := ((-93083130472489362150374 : Int)/10^30,(-724049122193453540052 : Int)/10^30)
theorem v111_pg_checked : Scalar.distance (sourceCoefficient 1 16 1 2) v111_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v111_mb : Scalar.QComplex := ((2983788952082618970973619 : Int)/10^30,(-431462722081892051423744091 : Int)/10^30)
theorem v111_mb_checked : Scalar.distance (sourceCoefficient 1 16 3 1) v111_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v111_mg : Scalar.QComplex := ((-93083720635168269048233 : Int)/10^30,(-643722303307687019819 : Int)/10^30)
theorem v111_mg_checked : Scalar.distance (sourceCoefficient 1 16 3 2) v111_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v111_upper : Scalar.QComplex := ((999981683953868788953181719941 : Int)/10^30,(6052417433131674947575207950 : Int)/10^30)
theorem v111_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 16 5) 1) 14) v111_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material111 : Material (1 : Basis) (16 : Basis) where
  plus := ![v111_pa,v111_pb,v111_pg]
  minus := ![(Primitive.Addresses.material111 1).one,v111_mb,v111_mg]
  upper := v111_upper
  lower := (Primitive.Addresses.material111 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v111_pa_checked.trans (by decide +kernel)
    · exact v111_pb_checked.trans (by decide +kernel)
    · exact v111_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 16 Primitive.Addresses.material111
    · exact v111_mb_checked.trans (by decide +kernel)
    · exact v111_mg_checked.trans (by decide +kernel)
  upper_error := v111_upper_checked
  lower_error := reuse_lower_error 1 16 Primitive.Addresses.material111

def v112_pa : Scalar.QComplex := ((999969800700771352782023965918 : Int)/10^30,(7771594846594908191078622729 : Int)/10^30)
theorem v112_pa_checked : Scalar.distance (sourceCoefficient 1 17 1 0) v112_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v112_pb : Scalar.QComplex := ((3353233588697616054187170 : Int)/10^30,(-431460001400130674718957359 : Int)/10^30)
theorem v112_pb_checked : Scalar.distance (sourceCoefficient 1 17 1 1) v112_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v112_pg : Scalar.QComplex := ((-93083134495462909705941 : Int)/10^30,(-723426255315794420033 : Int)/10^30)
theorem v112_pg_checked : Scalar.distance (sourceCoefficient 1 17 1 2) v112_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v112_mb : Scalar.QComplex := ((2980901791164292376869900 : Int)/10^30,(-431462734437416468746367816 : Int)/10^30)
theorem v112_mb_checked : Scalar.distance (sourceCoefficient 1 17 3 1) v112_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v112_mg : Scalar.QComplex := ((-93083724120634256129867 : Int)/10^30,(-643099433190304721238 : Int)/10^30)
theorem v112_mg_checked : Scalar.distance (sourceCoefficient 1 17 3 2) v112_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v112_upper : Scalar.QComplex := ((999981724430889558967346463863 : Int)/10^30,(6045726112259449253774546576 : Int)/10^30)
theorem v112_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 17 5) 1) 14) v112_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material112 : Material (1 : Basis) (17 : Basis) where
  plus := ![v112_pa,v112_pb,v112_pg]
  minus := ![(Primitive.Addresses.material112 1).one,v112_mb,v112_mg]
  upper := v112_upper
  lower := (Primitive.Addresses.material112 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v112_pa_checked.trans (by decide +kernel)
    · exact v112_pb_checked.trans (by decide +kernel)
    · exact v112_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 17 Primitive.Addresses.material112
    · exact v112_mb_checked.trans (by decide +kernel)
    · exact v112_mg_checked.trans (by decide +kernel)
  upper_error := v112_upper_checked
  lower_error := reuse_lower_error 1 17 Primitive.Addresses.material112

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
