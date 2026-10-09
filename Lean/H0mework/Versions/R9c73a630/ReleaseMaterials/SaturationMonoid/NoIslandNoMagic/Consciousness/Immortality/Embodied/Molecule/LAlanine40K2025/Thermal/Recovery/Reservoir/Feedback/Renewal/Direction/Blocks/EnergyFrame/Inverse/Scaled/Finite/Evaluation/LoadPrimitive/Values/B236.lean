import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B157
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B158

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3777_pa : Scalar.QComplex := ((999998848464834268355204318367 : Int)/10^30,(-1517586572631048180610284932 : Int)/10^30)
theorem v3777_pa_checked : Scalar.distance (sourceCoefficient 53 68 1 0) v3777_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3777_pb : Scalar.QComplex := ((-654804483478973450854504 : Int)/10^30,(-431477018351148970673088968 : Int)/10^30)
theorem v3777_pb_checked : Scalar.distance (sourceCoefficient 53 68 1 1) v3777_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3777_pg : Scalar.QComplex := ((-93086322080334344749287 : Int)/10^30,(141266715158314713245 : Int)/10^30)
theorem v3777_pg_checked : Scalar.distance (sourceCoefficient 53 68 1 2) v3777_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3777_mb : Scalar.QComplex := ((-1027149473498860234039181 : Int)/10^30,(-431476292625757621453223979 : Int)/10^30)
theorem v3777_mb_checked : Scalar.distance (sourceCoefficient 53 68 3 1) v3777_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3777_mg : Scalar.QComplex := ((-93086165513229614198399 : Int)/10^30,(221595966061273638690 : Int)/10^30)
theorem v3777_mg_checked : Scalar.distance (sourceCoefficient 53 68 3 2) v3777_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3777_upper : Scalar.QComplex := ((999994739867267613637064700254 : Int)/10^30,(-3243491605627547103329284973 : Int)/10^30)
theorem v3777_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 68 5) 1) 14) v3777_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3777 : Material (53 : Basis) (68 : Basis) where
  plus := ![v3777_pa,v3777_pb,v3777_pg]
  minus := ![(Primitive.Addresses.material3777 1).one,v3777_mb,v3777_mg]
  upper := v3777_upper
  lower := (Primitive.Addresses.material3777 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3777_pa_checked.trans (by decide +kernel)
    · exact v3777_pb_checked.trans (by decide +kernel)
    · exact v3777_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 68 Primitive.Addresses.material3777
    · exact v3777_mb_checked.trans (by decide +kernel)
    · exact v3777_mg_checked.trans (by decide +kernel)
  upper_error := v3777_upper_checked
  lower_error := reuse_lower_error 53 68 Primitive.Addresses.material3777

def v3778_pa : Scalar.QComplex := ((999998815397215567586512741106 : Int)/10^30,(-1539221935128612338309143405 : Int)/10^30)
theorem v3778_pa_checked : Scalar.distance (sourceCoefficient 53 69 1 0) v3778_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3778_pb : Scalar.QComplex := ((-664139654519513152662914 : Int)/10^30,(-431477003166756384980057165 : Int)/10^30)
theorem v3778_pb_checked : Scalar.distance (sourceCoefficient 53 69 1 1) v3778_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3778_pg : Scalar.QComplex := ((-93086318903329966430321 : Int)/10^30,(143280673647067635679 : Int)/10^30)
theorem v3778_pg_checked : Scalar.distance (sourceCoefficient 53 69 1 2) v3778_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3778_mb : Scalar.QComplex := ((-1036484627960042197263909 : Int)/10^30,(-431476269385538522113931246 : Int)/10^30)
theorem v3778_mb_checked : Scalar.distance (sourceCoefficient 53 69 3 1) v3778_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3778_mg : Scalar.QComplex := ((-93086160598270948352781 : Int)/10^30,(223609921058526081788 : Int)/10^30)
theorem v3778_mg_checked : Scalar.distance (sourceCoefficient 53 69 3 2) v3778_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3778_upper : Scalar.QComplex := ((999994669459025237159954780167 : Int)/10^30,(-3265126878830070282521765138 : Int)/10^30)
theorem v3778_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 69 5) 1) 14) v3778_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3778 : Material (53 : Basis) (69 : Basis) where
  plus := ![v3778_pa,v3778_pb,v3778_pg]
  minus := ![(Primitive.Addresses.material3778 1).one,v3778_mb,v3778_mg]
  upper := v3778_upper
  lower := (Primitive.Addresses.material3778 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3778_pa_checked.trans (by decide +kernel)
    · exact v3778_pb_checked.trans (by decide +kernel)
    · exact v3778_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 69 Primitive.Addresses.material3778
    · exact v3778_mb_checked.trans (by decide +kernel)
    · exact v3778_mg_checked.trans (by decide +kernel)
  upper_error := v3778_upper_checked
  lower_error := reuse_lower_error 53 69 Primitive.Addresses.material3778

def v3779_pa : Scalar.QComplex := ((999998793389786757439365559591 : Int)/10^30,(-1553453884277520021812940558 : Int)/10^30)
theorem v3779_pa_checked : Scalar.distance (sourceCoefficient 53 70 1 0) v3779_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3779_pb : Scalar.QComplex := ((-670280419568339482181365 : Int)/10^30,(-431476993031481576955761188 : Int)/10^30)
theorem v3779_pb_checked : Scalar.distance (sourceCoefficient 53 70 1 1) v3779_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3779_pg : Scalar.QComplex := ((-93086316785747614181959 : Int)/10^30,(144605474866350208288 : Int)/10^30)
theorem v3779_pg_checked : Scalar.distance (sourceCoefficient 53 70 1 2) v3779_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3779_mb : Scalar.QComplex := ((-1042625381976095368784559 : Int)/10^30,(-431476253951063820569574766 : Int)/10^30)
theorem v3779_mb_checked : Scalar.distance (sourceCoefficient 53 70 3 1) v3779_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3779_mg : Scalar.QComplex := ((-93086157337445599168226 : Int)/10^30,(224934719957146416430 : Int)/10^30)
theorem v3779_mg_checked : Scalar.distance (sourceCoefficient 53 70 3 2) v3779_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3779_upper : Scalar.QComplex := ((999994622888576085819357176844 : Int)/10^30,(-3279358768799335882944187967 : Int)/10^30)
theorem v3779_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 70 5) 1) 14) v3779_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3779 : Material (53 : Basis) (70 : Basis) where
  plus := ![v3779_pa,v3779_pb,v3779_pg]
  minus := ![(Primitive.Addresses.material3779 1).one,v3779_mb,v3779_mg]
  upper := v3779_upper
  lower := (Primitive.Addresses.material3779 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3779_pa_checked.trans (by decide +kernel)
    · exact v3779_pb_checked.trans (by decide +kernel)
    · exact v3779_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 70 Primitive.Addresses.material3779
    · exact v3779_mb_checked.trans (by decide +kernel)
    · exact v3779_mg_checked.trans (by decide +kernel)
  upper_error := v3779_upper_checked
  lower_error := reuse_lower_error 53 70 Primitive.Addresses.material3779

def v3780_pa : Scalar.QComplex := ((999998755356946486835913102153 : Int)/10^30,(-1577746671012174094526264226 : Int)/10^30)
theorem v3780_pa_checked : Scalar.distance (sourceCoefficient 53 71 1 0) v3780_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3780_pb : Scalar.QComplex := ((-680762208959811299125584 : Int)/10^30,(-431476975462180507135542496 : Int)/10^30)
theorem v3780_pb_checked : Scalar.distance (sourceCoefficient 53 71 1 1) v3780_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3780_pg : Scalar.QComplex := ((-93086313120387249032091 : Int)/10^30,(146866803439234538293 : Int)/10^30)
theorem v3780_pg_checked : Scalar.distance (sourceCoefficient 53 71 1 2) v3780_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3780_mb : Scalar.QComplex := ((-1053107152303202422534701 : Int)/10^30,(-431476227336457130032597363 : Int)/10^30)
theorem v3780_mb_checked : Scalar.distance (sourceCoefficient 53 71 3 1) v3780_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3780_mg : Scalar.QComplex := ((-93086151720661886858564 : Int)/10^30,(227196044524993857506 : Int)/10^30)
theorem v3780_mg_checked : Scalar.distance (sourceCoefficient 53 71 3 2) v3780_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3780_upper : Scalar.QComplex := ((999994542928646381048143402443 : Int)/10^30,(-3303651453711505750832209930 : Int)/10^30)
theorem v3780_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 71 5) 1) 14) v3780_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3780 : Material (53 : Basis) (71 : Basis) where
  plus := ![v3780_pa,v3780_pb,v3780_pg]
  minus := ![(Primitive.Addresses.material3780 1).one,v3780_mb,v3780_mg]
  upper := v3780_upper
  lower := (Primitive.Addresses.material3780 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3780_pa_checked.trans (by decide +kernel)
    · exact v3780_pb_checked.trans (by decide +kernel)
    · exact v3780_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 71 Primitive.Addresses.material3780
    · exact v3780_mb_checked.trans (by decide +kernel)
    · exact v3780_mg_checked.trans (by decide +kernel)
  upper_error := v3780_upper_checked
  lower_error := reuse_lower_error 53 71 Primitive.Addresses.material3780

def v3781_pa : Scalar.QComplex := ((999998713415907212255575887328 : Int)/10^30,(-1604109263821159108314334282 : Int)/10^30)
theorem v3781_pa_checked : Scalar.distance (sourceCoefficient 53 72 1 0) v3781_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3781_pb : Scalar.QComplex := ((-692137072756427586884959 : Int)/10^30,(-431476956011797880463136538 : Int)/10^30)
theorem v3781_pb_checked : Scalar.distance (sourceCoefficient 53 72 1 1) v3781_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3781_pg : Scalar.QComplex := ((-93086309070215626430240 : Int)/10^30,(149320802828222115402 : Int)/10^30)
theorem v3781_pg_checked : Scalar.distance (sourceCoefficient 53 72 1 2) v3781_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3781_mb : Scalar.QComplex := ((-1064481995079632867752971 : Int)/10^30,(-431476198070086593994463096 : Int)/10^30)
theorem v3781_mb_checked : Scalar.distance (sourceCoefficient 53 72 3 1) v3781_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3781_mg : Scalar.QComplex := ((-93086145552800823654067 : Int)/10^30,(229650039505129611436 : Int)/10^30)
theorem v3781_mg_checked : Scalar.distance (sourceCoefficient 53 72 3 2) v3781_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3781_upper : Scalar.QComplex := ((999994455488225980148441782727 : Int)/10^30,(-3330013934870076616759892664 : Int)/10^30)
theorem v3781_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 72 5) 1) 14) v3781_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3781 : Material (53 : Basis) (72 : Basis) where
  plus := ![v3781_pa,v3781_pb,v3781_pg]
  minus := ![(Primitive.Addresses.material3781 1).one,v3781_mb,v3781_mg]
  upper := v3781_upper
  lower := (Primitive.Addresses.material3781 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3781_pa_checked.trans (by decide +kernel)
    · exact v3781_pb_checked.trans (by decide +kernel)
    · exact v3781_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 72 Primitive.Addresses.material3781
    · exact v3781_mb_checked.trans (by decide +kernel)
    · exact v3781_mg_checked.trans (by decide +kernel)
  upper_error := v3781_upper_checked
  lower_error := reuse_lower_error 53 72 Primitive.Addresses.material3781

def v3782_pa : Scalar.QComplex := ((999998698213000114057462710821 : Int)/10^30,(-1613558894221866325781034189 : Int)/10^30)
theorem v3782_pa_checked : Scalar.distance (sourceCoefficient 53 73 1 0) v3782_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3782_pb : Scalar.QComplex := ((-696214374940696624803913 : Int)/10^30,(-431476948942493318106701173 : Int)/10^30)
theorem v3782_pb_checked : Scalar.distance (sourceCoefficient 53 73 1 1) v3782_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3782_pg : Scalar.QComplex := ((-93086307600061916337858 : Int)/10^30,(150200435087326190999 : Int)/10^30)
theorem v3782_pg_checked : Scalar.distance (sourceCoefficient 53 73 1 2) v3782_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3782_mb : Scalar.QComplex := ((-1068559289645244512897968 : Int)/10^30,(-431476187482256513712552294 : Int)/10^30)
theorem v3782_mb_checked : Scalar.distance (sourceCoefficient 53 73 3 1) v3782_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3782_mg : Scalar.QComplex := ((-93086143323564638526575 : Int)/10^30,(230529670168029957244 : Int)/10^30)
theorem v3782_mg_checked : Scalar.distance (sourceCoefficient 53 73 3 2) v3782_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3782_upper : Scalar.QComplex := ((999994423976136717047310165824 : Int)/10^30,(-3339463524957830929403833376 : Int)/10^30)
theorem v3782_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 73 5) 1) 14) v3782_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3782 : Material (53 : Basis) (73 : Basis) where
  plus := ![v3782_pa,v3782_pb,v3782_pg]
  minus := ![(Primitive.Addresses.material3782 1).one,v3782_mb,v3782_mg]
  upper := v3782_upper
  lower := (Primitive.Addresses.material3782 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3782_pa_checked.trans (by decide +kernel)
    · exact v3782_pb_checked.trans (by decide +kernel)
    · exact v3782_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 73 Primitive.Addresses.material3782
    · exact v3782_mb_checked.trans (by decide +kernel)
    · exact v3782_mg_checked.trans (by decide +kernel)
  upper_error := v3782_upper_checked
  lower_error := reuse_lower_error 53 73 Primitive.Addresses.material3782

def v3783_pa : Scalar.QComplex := ((999998680999220806883569967896 : Int)/10^30,(-1624192051028195787240411998 : Int)/10^30)
theorem v3783_pa_checked : Scalar.distance (sourceCoefficient 53 74 1 0) v3783_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3783_pb : Scalar.QComplex := ((-700802342013394454320944 : Int)/10^30,(-431476940926361821153427048 : Int)/10^30)
theorem v3783_pb_checked : Scalar.distance (sourceCoefficient 53 74 1 1) v3783_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3783_pg : Scalar.QComplex := ((-93086305934182109419732 : Int)/10^30,(151190237577918524650 : Int)/10^30)
theorem v3783_pg_checked : Scalar.distance (sourceCoefficient 53 74 1 2) v3783_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3783_mb : Scalar.QComplex := ((-1073147248092072072085716 : Int)/10^30,(-431476175506919052159488991 : Int)/10^30)
theorem v3783_mb_checked : Scalar.distance (sourceCoefficient 53 74 3 1) v3783_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3783_mg : Scalar.QComplex := ((-93086140803530481559776 : Int)/10^30,(231519470852494342510 : Int)/10^30)
theorem v3783_mg_checked : Scalar.distance (sourceCoefficient 53 74 3 2) v3783_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3783_upper : Scalar.QComplex := ((999994388410519032501147452109 : Int)/10^30,(-3350096636217900923853400049 : Int)/10^30)
theorem v3783_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 74 5) 1) 14) v3783_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3783 : Material (53 : Basis) (74 : Basis) where
  plus := ![v3783_pa,v3783_pb,v3783_pg]
  minus := ![(Primitive.Addresses.material3783 1).one,v3783_mb,v3783_mg]
  upper := v3783_upper
  lower := (Primitive.Addresses.material3783 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3783_pa_checked.trans (by decide +kernel)
    · exact v3783_pb_checked.trans (by decide +kernel)
    · exact v3783_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 74 Primitive.Addresses.material3783
    · exact v3783_mb_checked.trans (by decide +kernel)
    · exact v3783_mg_checked.trans (by decide +kernel)
  upper_error := v3783_upper_checked
  lower_error := reuse_lower_error 53 74 Primitive.Addresses.material3783

def v3784_pa : Scalar.QComplex := ((999998656826862268361115861297 : Int)/10^30,(-1639007160249521254183839541 : Int)/10^30)
theorem v3784_pa_checked : Scalar.distance (sourceCoefficient 53 75 1 0) v3784_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3784_pb : Scalar.QComplex := ((-707194727062292666778291 : Int)/10^30,(-431476929649086747498565999 : Int)/10^30)
theorem v3784_pb_checked : Scalar.distance (sourceCoefficient 53 75 1 1) v3784_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3784_pg : Scalar.QComplex := ((-93086303592650100793834 : Int)/10^30,(152569323036530594364 : Int)/10^30)
theorem v3784_pg_checked : Scalar.distance (sourceCoefficient 53 75 1 2) v3784_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3784_mb : Scalar.QComplex := ((-1079539621029012705459879 : Int)/10^30,(-431476158713307782685542771 : Int)/10^30)
theorem v3784_mb_checked : Scalar.distance (sourceCoefficient 53 75 3 1) v3784_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3784_mg : Scalar.QComplex := ((-93086137271910705714403 : Int)/10^30,(232898553776973203906 : Int)/10^30)
theorem v3784_mg_checked : Scalar.distance (sourceCoefficient 53 75 3 2) v3784_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3784_upper : Scalar.QComplex := ((999994338668661996069176011392 : Int)/10^30,(-3364911681654563572358308751 : Int)/10^30)
theorem v3784_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 75 5) 1) 14) v3784_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3784 : Material (53 : Basis) (75 : Basis) where
  plus := ![v3784_pa,v3784_pb,v3784_pg]
  minus := ![(Primitive.Addresses.material3784 1).one,v3784_mb,v3784_mg]
  upper := v3784_upper
  lower := (Primitive.Addresses.material3784 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3784_pa_checked.trans (by decide +kernel)
    · exact v3784_pb_checked.trans (by decide +kernel)
    · exact v3784_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 75 Primitive.Addresses.material3784
    · exact v3784_mb_checked.trans (by decide +kernel)
    · exact v3784_mg_checked.trans (by decide +kernel)
  upper_error := v3784_upper_checked
  lower_error := reuse_lower_error 53 75 Primitive.Addresses.material3784

def v3785_pa : Scalar.QComplex := ((999998636376445457275722857673 : Int)/10^30,(-1651437328394950036636974939 : Int)/10^30)
theorem v3785_pa_checked : Scalar.distance (sourceCoefficient 53 76 1 0) v3785_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3785_pb : Scalar.QComplex := ((-712558063838163055208814 : Int)/10^30,(-431476920089813666082995742 : Int)/10^30)
theorem v3785_pb_checked : Scalar.distance (sourceCoefficient 53 76 1 1) v3785_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3785_pg : Scalar.QComplex := ((-93086301609669044732696 : Int)/10^30,(153726402865382286788 : Int)/10^30)
theorem v3785_pg_checked : Scalar.distance (sourceCoefficient 53 76 1 2) v3785_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3785_mb : Scalar.QComplex := ((-1084902947558645560049982 : Int)/10^30,(-431476144525720178769491199 : Int)/10^30)
theorem v3785_mb_checked : Scalar.distance (sourceCoefficient 53 76 3 1) v3785_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3785_mg : Scalar.QComplex := ((-93086134290422608649696 : Int)/10^30,(234055631463767853659 : Int)/10^30)
theorem v3785_mg_checked : Scalar.distance (sourceCoefficient 53 76 3 2) v3785_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3785_upper : Scalar.QComplex := ((999994296764933080512657579587 : Int)/10^30,(-3377341795991152883702902977 : Int)/10^30)
theorem v3785_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 76 5) 1) 14) v3785_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3785 : Material (53 : Basis) (76 : Basis) where
  plus := ![v3785_pa,v3785_pb,v3785_pg]
  minus := ![(Primitive.Addresses.material3785 1).one,v3785_mb,v3785_mg]
  upper := v3785_upper
  lower := (Primitive.Addresses.material3785 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3785_pa_checked.trans (by decide +kernel)
    · exact v3785_pb_checked.trans (by decide +kernel)
    · exact v3785_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 76 Primitive.Addresses.material3785
    · exact v3785_mb_checked.trans (by decide +kernel)
    · exact v3785_mg_checked.trans (by decide +kernel)
  upper_error := v3785_upper_checked
  lower_error := reuse_lower_error 53 76 Primitive.Addresses.material3785

def v3786_pa : Scalar.QComplex := ((999998631619974549945311325915 : Int)/10^30,(-1654315017895991696378662147 : Int)/10^30)
theorem v3786_pa_checked : Scalar.distance (sourceCoefficient 53 77 1 0) v3786_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3786_pb : Scalar.QComplex := ((-713799721847319771403710 : Int)/10^30,(-431476917864089296446882101 : Int)/10^30)
theorem v3786_pb_checked : Scalar.distance (sourceCoefficient 53 77 1 1) v3786_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3786_pg : Scalar.QComplex := ((-93086301148200077426473 : Int)/10^30,(153994276672548515827 : Int)/10^30)
theorem v3786_pg_checked : Scalar.distance (sourceCoefficient 53 77 1 2) v3786_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3786_mb : Scalar.QComplex := ((-1086144603184776364769928 : Int)/10^30,(-431476141228501698170837671 : Int)/10^30)
theorem v3786_mb_checked : Scalar.distance (sourceCoefficient 53 77 3 1) v3786_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3786_mg : Scalar.QComplex := ((-93086133597790782173420 : Int)/10^30,(234323504772965486858 : Int)/10^30)
theorem v3786_mg_checked : Scalar.distance (sourceCoefficient 53 77 3 2) v3786_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3786_upper : Scalar.QComplex := ((999994287041838240541253922878 : Int)/10^30,(-3380219472996976786415346354 : Int)/10^30)
theorem v3786_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 77 5) 1) 14) v3786_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3786 : Material (53 : Basis) (77 : Basis) where
  plus := ![v3786_pa,v3786_pb,v3786_pg]
  minus := ![(Primitive.Addresses.material3786 1).one,v3786_mb,v3786_mg]
  upper := v3786_upper
  lower := (Primitive.Addresses.material3786 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3786_pa_checked.trans (by decide +kernel)
    · exact v3786_pb_checked.trans (by decide +kernel)
    · exact v3786_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 77 Primitive.Addresses.material3786
    · exact v3786_mb_checked.trans (by decide +kernel)
    · exact v3786_mg_checked.trans (by decide +kernel)
  upper_error := v3786_upper_checked
  lower_error := reuse_lower_error 53 77 Primitive.Addresses.material3786

def v3787_pa : Scalar.QComplex := ((999998602851366557489946916769 : Int)/10^30,(-1671614583228058637019299624 : Int)/10^30)
theorem v3787_pa_checked : Scalar.distance (sourceCoefficient 53 78 1 0) v3787_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3787_pb : Scalar.QComplex := ((-721264093406667712176736 : Int)/10^30,(-431476904383480855994071838 : Int)/10^30)
theorem v3787_pb_checked : Scalar.distance (sourceCoefficient 53 78 1 1) v3787_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3787_pg : Scalar.QComplex := ((-93086298355071626682457 : Int)/10^30,(155604631231853660410 : Int)/10^30)
theorem v3787_pg_checked : Scalar.distance (sourceCoefficient 53 78 1 2) v3787_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3787_mb : Scalar.QComplex := ((-1093608960331639695319998 : Int)/10^30,(-431476121306481804262711456 : Int)/10^30)
theorem v3787_mb_checked : Scalar.distance (sourceCoefficient 53 78 3 1) v3787_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3787_mg : Scalar.QComplex := ((-93086129414999914435437 : Int)/10^30,(235933856322317977015 : Int)/10^30)
theorem v3787_mg_checked : Scalar.distance (sourceCoefficient 53 78 3 2) v3787_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3787_upper : Scalar.QComplex := ((999994228415792736707968091439 : Int)/10^30,(-3397518962911365787388859230 : Int)/10^30)
theorem v3787_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 78 5) 1) 14) v3787_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3787 : Material (53 : Basis) (78 : Basis) where
  plus := ![v3787_pa,v3787_pb,v3787_pg]
  minus := ![(Primitive.Addresses.material3787 1).one,v3787_mb,v3787_mg]
  upper := v3787_upper
  lower := (Primitive.Addresses.material3787 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3787_pa_checked.trans (by decide +kernel)
    · exact v3787_pb_checked.trans (by decide +kernel)
    · exact v3787_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 78 Primitive.Addresses.material3787
    · exact v3787_mb_checked.trans (by decide +kernel)
    · exact v3787_mg_checked.trans (by decide +kernel)
  upper_error := v3787_upper_checked
  lower_error := reuse_lower_error 53 78 Primitive.Addresses.material3787

def v3788_pa : Scalar.QComplex := ((999998593513084614330861434969 : Int)/10^30,(-1677191656479931075272803897 : Int)/10^30)
theorem v3788_pa_checked : Scalar.distance (sourceCoefficient 53 79 1 0) v3788_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3788_pb : Scalar.QComplex := ((-723670474478340734080814 : Int)/10^30,(-431476900000871550235614853 : Int)/10^30)
theorem v3788_pb_checked : Scalar.distance (sourceCoefficient 53 79 1 1) v3788_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3788_pg : Scalar.QComplex := ((-93086297447688591366625 : Int)/10^30,(156123780997927562877 : Int)/10^30)
theorem v3788_pg_checked : Scalar.distance (sourceCoefficient 53 79 1 2) v3788_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3788_mb : Scalar.QComplex := ((-1096015336725312621718551 : Int)/10^30,(-431476114847275644876412686 : Int)/10^30)
theorem v3788_mb_checked : Scalar.distance (sourceCoefficient 53 79 3 1) v3788_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3788_mg : Scalar.QComplex := ((-93086128059614350495497 : Int)/10^30,(236453005112058002794 : Int)/10^30)
theorem v3788_mg_checked : Scalar.distance (sourceCoefficient 53 79 3 2) v3788_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3788_upper : Scalar.QComplex := ((999994209452002217224216810324 : Int)/10^30,(-3403096011739815274450469992 : Int)/10^30)
theorem v3788_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 79 5) 1) 14) v3788_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3788 : Material (53 : Basis) (79 : Basis) where
  plus := ![v3788_pa,v3788_pb,v3788_pg]
  minus := ![(Primitive.Addresses.material3788 1).one,v3788_mb,v3788_mg]
  upper := v3788_upper
  lower := (Primitive.Addresses.material3788 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3788_pa_checked.trans (by decide +kernel)
    · exact v3788_pb_checked.trans (by decide +kernel)
    · exact v3788_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 79 Primitive.Addresses.material3788
    · exact v3788_mb_checked.trans (by decide +kernel)
    · exact v3788_mg_checked.trans (by decide +kernel)
  upper_error := v3788_upper_checked
  lower_error := reuse_lower_error 53 79 Primitive.Addresses.material3788

def v3789_pa : Scalar.QComplex := ((999998578863522612484456641005 : Int)/10^30,(-1685903596041643101554835011 : Int)/10^30)
theorem v3789_pa_checked : Scalar.distance (sourceCoefficient 53 80 1 0) v3789_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3789_pb : Scalar.QComplex := ((-727429479494756169665048 : Int)/10^30,(-431476893118994270520896167 : Int)/10^30)
theorem v3789_pb_checked : Scalar.distance (sourceCoefficient 53 80 1 1) v3789_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3789_pg : Scalar.QComplex := ((-93086296023507006700919 : Int)/10^30,(156934744233916965506 : Int)/10^30)
theorem v3789_pg_checked : Scalar.distance (sourceCoefficient 53 80 1 2) v3789_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3789_mb : Scalar.QComplex := ((-1099774334403328550528278 : Int)/10^30,(-431476104721548897733855533 : Int)/10^30)
theorem v3789_mb_checked : Scalar.distance (sourceCoefficient 53 80 3 1) v3789_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3789_mg : Scalar.QComplex := ((-93086125935608547887127 : Int)/10^30,(237263966817084165005 : Int)/10^30)
theorem v3789_mg_checked : Scalar.distance (sourceCoefficient 53 80 3 2) v3789_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3789_upper : Scalar.QComplex := ((999994179766444691647831529832 : Int)/10^30,(-3411807913042301682567972571 : Int)/10^30)
theorem v3789_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 80 5) 1) 14) v3789_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3789 : Material (53 : Basis) (80 : Basis) where
  plus := ![v3789_pa,v3789_pb,v3789_pg]
  minus := ![(Primitive.Addresses.material3789 1).one,v3789_mb,v3789_mg]
  upper := v3789_upper
  lower := (Primitive.Addresses.material3789 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3789_pa_checked.trans (by decide +kernel)
    · exact v3789_pb_checked.trans (by decide +kernel)
    · exact v3789_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 80 Primitive.Addresses.material3789
    · exact v3789_mb_checked.trans (by decide +kernel)
    · exact v3789_mg_checked.trans (by decide +kernel)
  upper_error := v3789_upper_checked
  lower_error := reuse_lower_error 53 80 Primitive.Addresses.material3789

def v3790_pa : Scalar.QComplex := ((999998534294602332978130143115 : Int)/10^30,(-1712135697613285262311463836 : Int)/10^30)
theorem v3790_pa_checked : Scalar.distance (sourceCoefficient 53 81 1 0) v3790_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3790_pb : Scalar.QComplex := ((-738748038261492375040865 : Int)/10^30,(-431476872133626668108710199 : Int)/10^30)
theorem v3790_pb_checked : Scalar.distance (sourceCoefficient 53 81 1 1) v3790_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3790_pg : Scalar.QComplex := ((-93086291685447467552761 : Int)/10^30,(159376596552235183840 : Int)/10^30)
theorem v3790_pg_checked : Scalar.distance (sourceCoefficient 53 81 1 2) v3790_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3790_mb : Scalar.QComplex := ((-1111092870846220948347865 : Int)/10^30,(-431476073968782662403101754 : Int)/10^30)
theorem v3790_mb_checked : Scalar.distance (sourceCoefficient 53 81 3 1) v3790_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3790_mg : Scalar.QComplex := ((-93086119490342050234053 : Int)/10^30,(239705814482639163728 : Int)/10^30)
theorem v3790_mg_checked : Scalar.distance (sourceCoefficient 53 81 3 2) v3790_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3790_upper : Scalar.QComplex := ((999994089923363237323391413798 : Int)/10^30,(-3438039898622396849909116200 : Int)/10^30)
theorem v3790_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 81 5) 1) 14) v3790_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3790 : Material (53 : Basis) (81 : Basis) where
  plus := ![v3790_pa,v3790_pb,v3790_pg]
  minus := ![(Primitive.Addresses.material3790 1).one,v3790_mb,v3790_mg]
  upper := v3790_upper
  lower := (Primitive.Addresses.material3790 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3790_pa_checked.trans (by decide +kernel)
    · exact v3790_pb_checked.trans (by decide +kernel)
    · exact v3790_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 81 Primitive.Addresses.material3790
    · exact v3790_mb_checked.trans (by decide +kernel)
    · exact v3790_mg_checked.trans (by decide +kernel)
  upper_error := v3790_upper_checked
  lower_error := reuse_lower_error 53 81 Primitive.Addresses.material3790

def v3791_pa : Scalar.QComplex := ((999998517226125918836177152340 : Int)/10^30,(-1722075941863182173185929137 : Int)/10^30)
theorem v3791_pa_checked : Scalar.distance (sourceCoefficient 53 82 1 0) v3791_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3791_pb : Scalar.QComplex := ((-743037028855396612678898 : Int)/10^30,(-431476864078121171423153086 : Int)/10^30)
theorem v3791_pb_checked : Scalar.distance (sourceCoefficient 53 82 1 1) v3791_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3791_pg : Scalar.QComplex := ((-93086290022083275107129 : Int)/10^30,(160301898255795092185 : Int)/10^30)
theorem v3791_pg_checked : Scalar.distance (sourceCoefficient 53 82 1 2) v3791_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3791_mb : Scalar.QComplex := ((-1115381852891599534181720 : Int)/10^30,(-431476062212074451576619144 : Int)/10^30)
theorem v3791_mb_checked : Scalar.distance (sourceCoefficient 53 82 3 1) v3791_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3791_mg : Scalar.QComplex := ((-93086117028484781004443 : Int)/10^30,(240631114406258576523 : Int)/10^30)
theorem v3791_mg_checked : Scalar.distance (sourceCoefficient 53 82 3 2) v3791_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3791_upper : Scalar.QComplex := ((999994055698952441264080066935 : Int)/10^30,(-3447980098608825762951115612 : Int)/10^30)
theorem v3791_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 82 5) 1) 14) v3791_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3791 : Material (53 : Basis) (82 : Basis) where
  plus := ![v3791_pa,v3791_pb,v3791_pg]
  minus := ![(Primitive.Addresses.material3791 1).one,v3791_mb,v3791_mg]
  upper := v3791_upper
  lower := (Primitive.Addresses.material3791 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3791_pa_checked.trans (by decide +kernel)
    · exact v3791_pb_checked.trans (by decide +kernel)
    · exact v3791_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 82 Primitive.Addresses.material3791
    · exact v3791_mb_checked.trans (by decide +kernel)
    · exact v3791_mg_checked.trans (by decide +kernel)
  upper_error := v3791_upper_checked
  lower_error := reuse_lower_error 53 82 Primitive.Addresses.material3791

def v3792_pa : Scalar.QComplex := ((999998493767876844360402346612 : Int)/10^30,(-1735644542403792531039421809 : Int)/10^30)
theorem v3792_pa_checked : Scalar.distance (sourceCoefficient 53 83 1 0) v3792_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3792_pb : Scalar.QComplex := ((-748891573071007613199941 : Int)/10^30,(-431476852990464658480391902 : Int)/10^30)
theorem v3792_pb_checked : Scalar.distance (sourceCoefficient 53 83 1 1) v3792_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3792_pg : Scalar.QComplex := ((-93086287734242254093088 : Int)/10^30,(161564950632885281859 : Int)/10^30)
theorem v3792_pg_checked : Scalar.distance (sourceCoefficient 53 83 1 2) v3792_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3792_mb : Scalar.QComplex := ((-1121236385359147956184383 : Int)/10^30,(-431476046072214087886066088 : Int)/10^30)
theorem v3792_mb_checked : Scalar.distance (sourceCoefficient 53 83 3 1) v3792_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3792_mg : Scalar.QComplex := ((-93086113650687296196706 : Int)/10^30,(241894164338752881260 : Int)/10^30)
theorem v3792_mg_checked : Scalar.distance (sourceCoefficient 53 83 3 2) v3792_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3792_upper : Scalar.QComplex := ((999994008822564705826741342548 : Int)/10^30,(-3461548638453789708535849784 : Int)/10^30)
theorem v3792_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 53 83 5) 1) 14) v3792_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3792 : Material (53 : Basis) (83 : Basis) where
  plus := ![v3792_pa,v3792_pb,v3792_pg]
  minus := ![(Primitive.Addresses.material3792 1).one,v3792_mb,v3792_mg]
  upper := v3792_upper
  lower := (Primitive.Addresses.material3792 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3792_pa_checked.trans (by decide +kernel)
    · exact v3792_pb_checked.trans (by decide +kernel)
    · exact v3792_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 53 83 Primitive.Addresses.material3792
    · exact v3792_mb_checked.trans (by decide +kernel)
    · exact v3792_mg_checked.trans (by decide +kernel)
  upper_error := v3792_upper_checked
  lower_error := reuse_lower_error 53 83 Primitive.Addresses.material3792

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
