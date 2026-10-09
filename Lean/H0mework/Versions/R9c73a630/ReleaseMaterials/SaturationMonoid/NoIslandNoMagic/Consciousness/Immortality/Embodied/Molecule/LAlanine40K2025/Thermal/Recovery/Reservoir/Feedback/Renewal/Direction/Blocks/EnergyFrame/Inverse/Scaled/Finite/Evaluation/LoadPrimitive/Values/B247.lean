import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B164
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B165

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3953_pa : Scalar.QComplex := ((999998547748002856020938623204 : Int)/10^30,(-1704259923031723149625697698 : Int)/10^30)
theorem v3953_pa_checked : Scalar.distance (sourceCoefficient 57 78 1 0) v3953_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3953_pb : Scalar.QComplex := ((-735349826619615968610239 : Int)/10^30,(-431476882586221476903144389 : Int)/10^30)
theorem v3953_pb_checked : Scalar.distance (sourceCoefficient 57 78 1 1) v3953_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3953_pg : Scalar.QComplex := ((-93086293439126955009152 : Int)/10^30,(158643469682170579729 : Int)/10^30)
theorem v3953_pg_checked : Scalar.distance (sourceCoefficient 57 78 1 2) v3953_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3953_mb : Scalar.QComplex := ((-1107694669489772594727245 : Int)/10^30,(-431476087353877176387244639 : Int)/10^30)
theorem v3953_mb_checked : Scalar.distance (sourceCoefficient 57 78 3 1) v3953_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3953_mg : Scalar.QComplex := ((-93086121876676354772665 : Int)/10^30,(238972689398897613778 : Int)/10^30)
theorem v3953_mg_checked : Scalar.distance (sourceCoefficient 57 78 3 2) v3953_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3953_upper : Scalar.QComplex := ((999994116969616166193883540103 : Int)/10^30,(-3430164158990224642799606548 : Int)/10^30)
theorem v3953_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 78 5) 1) 14) v3953_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3953 : Material (57 : Basis) (78 : Basis) where
  plus := ![v3953_pa,v3953_pb,v3953_pg]
  minus := ![(Primitive.Addresses.material3953 1).one,v3953_mb,v3953_mg]
  upper := v3953_upper
  lower := (Primitive.Addresses.material3953 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3953_pa_checked.trans (by decide +kernel)
    · exact v3953_pb_checked.trans (by decide +kernel)
    · exact v3953_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 78 Primitive.Addresses.material3953
    · exact v3953_mb_checked.trans (by decide +kernel)
    · exact v3953_mg_checked.trans (by decide +kernel)
  upper_error := v3953_upper_checked
  lower_error := reuse_lower_error 57 78 Primitive.Addresses.material3953

def v3954_pa : Scalar.QComplex := ((999998538227655207079984127235 : Int)/10^30,(-1709836995975771963690013091 : Int)/10^30)
theorem v3954_pa_checked : Scalar.distance (sourceCoefficient 57 79 1 0) v3954_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3954_pb : Scalar.QComplex := ((-737756207602743009810484 : Int)/10^30,(-431476878151240666152551674 : Int)/10^30)
theorem v3954_pb_checked : Scalar.distance (sourceCoefficient 57 79 1 1) v3954_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3954_pg : Scalar.QComplex := ((-93086292517620714389719 : Int)/10^30,(159162619424365980623 : Int)/10^30)
theorem v3954_pg_checked : Scalar.distance (sourceCoefficient 57 79 1 2) v3954_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3954_mb : Scalar.QComplex := ((-1110101045749705323308492 : Int)/10^30,(-431476080842299607920308329 : Int)/10^30)
theorem v3954_mb_checked : Scalar.distance (sourceCoefficient 57 79 3 1) v3954_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3954_mg : Scalar.QComplex := ((-93086120507167611393911 : Int)/10^30,(239491838152571456784 : Int)/10^30)
theorem v3954_mg_checked : Scalar.distance (sourceCoefficient 57 79 3 2) v3954_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3954_upper : Scalar.QComplex := ((999994097823760743369394876257 : Int)/10^30,(-3435741207196622072831457047 : Int)/10^30)
theorem v3954_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 79 5) 1) 14) v3954_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3954 : Material (57 : Basis) (79 : Basis) where
  plus := ![v3954_pa,v3954_pb,v3954_pg]
  minus := ![(Primitive.Addresses.material3954 1).one,v3954_mb,v3954_mg]
  upper := v3954_upper
  lower := (Primitive.Addresses.material3954 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3954_pa_checked.trans (by decide +kernel)
    · exact v3954_pb_checked.trans (by decide +kernel)
    · exact v3954_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 79 Primitive.Addresses.material3954
    · exact v3954_mb_checked.trans (by decide +kernel)
    · exact v3954_mg_checked.trans (by decide +kernel)
  upper_error := v3954_upper_checked
  lower_error := reuse_lower_error 57 79 Primitive.Addresses.material3954

def v3955_pa : Scalar.QComplex := ((999998523293688580583081272627 : Int)/10^30,(-1718548935054601129676828691 : Int)/10^30)
theorem v3955_pa_checked : Scalar.distance (sourceCoefficient 57 80 1 0) v3955_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3955_pb : Scalar.QComplex := ((-741515212480256382512511 : Int)/10^30,(-431476871187553920198180609 : Int)/10^30)
theorem v3955_pb_checked : Scalar.distance (sourceCoefficient 57 80 1 1) v3955_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3955_pg : Scalar.QComplex := ((-93086291071377287355023 : Int)/10^30,(159973582622897182425 : Int)/10^30)
theorem v3955_pg_checked : Scalar.distance (sourceCoefficient 57 80 1 2) v3955_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3955_mb : Scalar.QComplex := ((-1113860043218221356152360 : Int)/10^30,(-431476070634763544865726306 : Int)/10^30)
theorem v3955_mb_checked : Scalar.distance (sourceCoefficient 57 80 3 1) v3955_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3955_mg : Scalar.QComplex := ((-93086118361100006955924 : Int)/10^30,(240302799801101055778 : Int)/10^30)
theorem v3955_mg_checked : Scalar.distance (sourceCoefficient 57 80 3 2) v3955_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3955_upper : Scalar.QComplex := ((999994067853799850141801516663 : Int)/10^30,(-3444453107525369758690283516 : Int)/10^30)
theorem v3955_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 80 5) 1) 14) v3955_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3955 : Material (57 : Basis) (80 : Basis) where
  plus := ![v3955_pa,v3955_pb,v3955_pg]
  minus := ![(Primitive.Addresses.material3955 1).one,v3955_mb,v3955_mg]
  upper := v3955_upper
  lower := (Primitive.Addresses.material3955 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3955_pa_checked.trans (by decide +kernel)
    · exact v3955_pb_checked.trans (by decide +kernel)
    · exact v3955_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 80 Primitive.Addresses.material3955
    · exact v3955_mb_checked.trans (by decide +kernel)
    · exact v3955_mg_checked.trans (by decide +kernel)
  upper_error := v3955_upper_checked
  lower_error := reuse_lower_error 57 80 Primitive.Addresses.material3955

def v3956_pa : Scalar.QComplex := ((999998477868411235431221078300 : Int)/10^30,(-1744781035157295616715691503 : Int)/10^30)
theorem v3956_pa_checked : Scalar.distance (sourceCoefficient 57 81 1 0) v3956_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3956_pb : Scalar.QComplex := ((-752833770824447331870458 : Int)/10^30,(-431476849955853775096096909 : Int)/10^30)
theorem v3956_pb_checked : Scalar.distance (sourceCoefficient 57 81 1 1) v3956_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3956_pg : Scalar.QComplex := ((-93086286666888397419869 : Int)/10^30,(162415434827266156664 : Int)/10^30)
theorem v3956_pg_checked : Scalar.distance (sourceCoefficient 57 81 1 2) v3956_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3956_mb : Scalar.QComplex := ((-1125178579025994765351486 : Int)/10^30,(-431476039635665223203463603 : Int)/10^30)
theorem v3956_mb_checked : Scalar.distance (sourceCoefficient 57 81 3 1) v3956_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3956_mg : Scalar.QComplex := ((-93086111849404281583602 : Int)/10^30,(242744647295381314973 : Int)/10^30)
theorem v3956_mg_checked : Scalar.distance (sourceCoefficient 57 81 3 2) v3956_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3956_upper : Scalar.QComplex := ((999993977154365140885505160776 : Int)/10^30,(-3470685090158524832940604441 : Int)/10^30)
theorem v3956_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 81 5) 1) 14) v3956_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3956 : Material (57 : Basis) (81 : Basis) where
  plus := ![v3956_pa,v3956_pb,v3956_pg]
  minus := ![(Primitive.Addresses.material3956 1).one,v3956_mb,v3956_mg]
  upper := v3956_upper
  lower := (Primitive.Addresses.material3956 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3956_pa_checked.trans (by decide +kernel)
    · exact v3956_pb_checked.trans (by decide +kernel)
    · exact v3956_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 81 Primitive.Addresses.material3956
    · exact v3956_mb_checked.trans (by decide +kernel)
    · exact v3956_mg_checked.trans (by decide +kernel)
  upper_error := v3956_upper_checked
  lower_error := reuse_lower_error 57 81 Primitive.Addresses.material3956

def v3957_pa : Scalar.QComplex := ((999998460475431716881849375154 : Int)/10^30,(-1754721278844688756664997682 : Int)/10^30)
theorem v3957_pa_checked : Scalar.distance (sourceCoefficient 57 82 1 0) v3957_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3957_pb : Scalar.QComplex := ((-757122761256546418952517 : Int)/10^30,(-431476841807004417661059223 : Int)/10^30)
theorem v3957_pb_checked : Scalar.distance (sourceCoefficient 57 82 1 1) v3957_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3957_pg : Scalar.QComplex := ((-93086284978351842419437 : Int)/10^30,(163340736487191509075 : Int)/10^30)
theorem v3957_pg_checked : Scalar.distance (sourceCoefficient 57 82 1 2) v3957_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3957_mb : Scalar.QComplex := ((-1129467560829016713101442 : Int)/10^30,(-431476027785613326014243298 : Int)/10^30)
theorem v3957_mb_checked : Scalar.distance (sourceCoefficient 57 82 3 1) v3957_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3957_mg : Scalar.QComplex := ((-93086109362374696826671 : Int)/10^30,(243669947153643572917 : Int)/10^30)
theorem v3957_mg_checked : Scalar.distance (sourceCoefficient 57 82 3 2) v3957_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3957_upper : Scalar.QComplex := ((999993942605452694558508977398 : Int)/10^30,(-3480625289022387893325199894 : Int)/10^30)
theorem v3957_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 82 5) 1) 14) v3957_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3957 : Material (57 : Basis) (82 : Basis) where
  plus := ![v3957_pa,v3957_pb,v3957_pg]
  minus := ![(Primitive.Addresses.material3957 1).one,v3957_mb,v3957_mg]
  upper := v3957_upper
  lower := (Primitive.Addresses.material3957 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3957_pa_checked.trans (by decide +kernel)
    · exact v3957_pb_checked.trans (by decide +kernel)
    · exact v3957_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 82 Primitive.Addresses.material3957
    · exact v3957_mb_checked.trans (by decide +kernel)
    · exact v3957_mg_checked.trans (by decide +kernel)
  upper_error := v3957_upper_checked
  lower_error := reuse_lower_error 57 82 Primitive.Addresses.material3957

def v3958_pa : Scalar.QComplex := ((999998436574230448641508462861 : Int)/10^30,(-1768289878612265338500654252 : Int)/10^30)
theorem v3958_pa_checked : Scalar.distance (sourceCoefficient 57 83 1 0) v3958_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3958_pb : Scalar.QComplex := ((-762977305249792961065485 : Int)/10^30,(-431476830591931965437972916 : Int)/10^30)
theorem v3958_pb_checked : Scalar.distance (sourceCoefficient 57 83 1 1) v3958_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3958_pg : Scalar.QComplex := ((-93086282656150123288791 : Int)/10^30,(164603788804315904277 : Int)/10^30)
theorem v3958_pg_checked : Scalar.distance (sourceCoefficient 57 83 1 2) v3958_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3958_mb : Scalar.QComplex := ((-1135322092964246542494439 : Int)/10^30,(-431476011518337262376655193 : Int)/10^30)
theorem v3958_mb_checked : Scalar.distance (sourceCoefficient 57 83 3 1) v3958_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3958_mg : Scalar.QComplex := ((-93086105950216578444166 : Int)/10^30,(244932996996520370585 : Int)/10^30)
theorem v3958_mg_checked : Scalar.distance (sourceCoefficient 57 83 3 2) v3958_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3958_upper : Scalar.QComplex := ((999993895286114759268032269425 : Int)/10^30,(-3494193827329823912106575041 : Int)/10^30)
theorem v3958_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 83 5) 1) 14) v3958_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3958 : Material (57 : Basis) (83 : Basis) where
  plus := ![v3958_pa,v3958_pb,v3958_pg]
  minus := ![(Primitive.Addresses.material3958 1).one,v3958_mb,v3958_mg]
  upper := v3958_upper
  lower := (Primitive.Addresses.material3958 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3958_pa_checked.trans (by decide +kernel)
    · exact v3958_pb_checked.trans (by decide +kernel)
    · exact v3958_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 83 Primitive.Addresses.material3958
    · exact v3958_mb_checked.trans (by decide +kernel)
    · exact v3958_mg_checked.trans (by decide +kernel)
  upper_error := v3958_upper_checked
  lower_error := reuse_lower_error 57 83 Primitive.Addresses.material3958

def v3959_pa : Scalar.QComplex := ((999998373820815589882200949702 : Int)/10^30,(-1803428879762519437220138150 : Int)/10^30)
theorem v3959_pa_checked : Scalar.distance (sourceCoefficient 57 84 1 0) v3959_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3959_pb : Scalar.QComplex := ((-778138989364645862819620 : Int)/10^30,(-431476801055601446089530013 : Int)/10^30)
theorem v3959_pb_checked : Scalar.distance (sourceCoefficient 57 84 1 1) v3959_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3959_pg : Scalar.QComplex := ((-93086276549338630862321 : Int)/10^30,(167874752433065845108 : Int)/10^30)
theorem v3959_pg_checked : Scalar.distance (sourceCoefficient 57 84 1 2) v3959_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3959_mb : Scalar.QComplex := ((-1150483745945188553840745 : Int)/10^30,(-431475968898167206539580596 : Int)/10^30)
theorem v3959_mb_checked : Scalar.distance (sourceCoefficient 57 84 3 1) v3959_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3959_mg : Scalar.QComplex := ((-93086097020713066984621 : Int)/10^30,(248203954137437784625 : Int)/10^30)
theorem v3959_mg_checked : Scalar.distance (sourceCoefficient 57 84 3 2) v3959_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3959_upper : Scalar.QComplex := ((999993771886065164292787540587 : Int)/10^30,(-3529332667837962413660568038 : Int)/10^30)
theorem v3959_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 84 5) 1) 14) v3959_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3959 : Material (57 : Basis) (84 : Basis) where
  plus := ![v3959_pa,v3959_pb,v3959_pg]
  minus := ![(Primitive.Addresses.material3959 1).one,v3959_mb,v3959_mg]
  upper := v3959_upper
  lower := (Primitive.Addresses.material3959 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3959_pa_checked.trans (by decide +kernel)
    · exact v3959_pb_checked.trans (by decide +kernel)
    · exact v3959_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 84 Primitive.Addresses.material3959
    · exact v3959_mb_checked.trans (by decide +kernel)
    · exact v3959_mg_checked.trans (by decide +kernel)
  upper_error := v3959_upper_checked
  lower_error := reuse_lower_error 57 84 Primitive.Addresses.material3959

def v3960_pa : Scalar.QComplex := ((999998228122482905769140037891 : Int)/10^30,(-1882485562929640673399123137 : Int)/10^30)
theorem v3960_pa_checked : Scalar.distance (sourceCoefficient 57 85 1 0) v3960_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3960_pb : Scalar.QComplex := ((-812250157951125720724832 : Int)/10^30,(-431476732007049662136141787 : Int)/10^30)
theorem v3960_pb_checked : Scalar.distance (sourceCoefficient 57 85 1 1) v3960_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3960_pg : Scalar.QComplex := ((-93086262319844979938461 : Int)/10^30,(175233855417118223732 : Int)/10^30)
theorem v3960_pg_checked : Scalar.distance (sourceCoefficient 57 85 1 2) v3960_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3960_mb : Scalar.QComplex := ((-1184594842244731031359254 : Int)/10^30,(-431475870413238952388205887 : Int)/10^30)
theorem v3960_mb_checked : Scalar.distance (sourceCoefficient 57 85 3 1) v3960_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3960_mg : Scalar.QComplex := ((-93086076440650280809072 : Int)/10^30,(255563042101947646522 : Int)/10^30)
theorem v3960_mg_checked : Scalar.distance (sourceCoefficient 57 85 3 2) v3960_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3960_upper : Scalar.QComplex := ((999993489743286300552672796939 : Int)/10^30,(-3608388981797336159480237120 : Int)/10^30)
theorem v3960_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 85 5) 1) 14) v3960_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3960 : Material (57 : Basis) (85 : Basis) where
  plus := ![v3960_pa,v3960_pb,v3960_pg]
  minus := ![(Primitive.Addresses.material3960 1).one,v3960_mb,v3960_mg]
  upper := v3960_upper
  lower := (Primitive.Addresses.material3960 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3960_pa_checked.trans (by decide +kernel)
    · exact v3960_pb_checked.trans (by decide +kernel)
    · exact v3960_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 85 Primitive.Addresses.material3960
    · exact v3960_mb_checked.trans (by decide +kernel)
    · exact v3960_mg_checked.trans (by decide +kernel)
  upper_error := v3960_upper_checked
  lower_error := reuse_lower_error 57 85 Primitive.Addresses.material3960

def v3961_pa : Scalar.QComplex := ((999998200560745213573389858062 : Int)/10^30,(-1897070180987309060168442145 : Int)/10^30)
theorem v3961_pa_checked : Scalar.distance (sourceCoefficient 57 86 1 0) v3961_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3961_pb : Scalar.QComplex := ((-818543090088297537197826 : Int)/10^30,(-431476718875908230413967905 : Int)/10^30)
theorem v3961_pb_checked : Scalar.distance (sourceCoefficient 57 86 1 1) v3961_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3961_pg : Scalar.QComplex := ((-93086259620584943723534 : Int)/10^30,(176591485151505161048 : Int)/10^30)
theorem v3961_pg_checked : Scalar.distance (sourceCoefficient 57 86 1 2) v3961_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3961_mb : Scalar.QComplex := ((-1190887760707172961036600 : Int)/10^30,(-431475851851585398753128854 : Int)/10^30)
theorem v3961_mb_checked : Scalar.distance (sourceCoefficient 57 86 3 1) v3961_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3961_mg : Scalar.QComplex := ((-93086072569817934249506 : Int)/10^30,(256920669001487145887 : Int)/10^30)
theorem v3961_mg_checked : Scalar.distance (sourceCoefficient 57 86 3 2) v3961_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3961_upper : Scalar.QComplex := ((999993437009861997006603563373 : Int)/10^30,(-3622973530563870303519026415 : Int)/10^30)
theorem v3961_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 86 5) 1) 14) v3961_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3961 : Material (57 : Basis) (86 : Basis) where
  plus := ![v3961_pa,v3961_pb,v3961_pg]
  minus := ![(Primitive.Addresses.material3961 1).one,v3961_mb,v3961_mg]
  upper := v3961_upper
  lower := (Primitive.Addresses.material3961 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3961_pa_checked.trans (by decide +kernel)
    · exact v3961_pb_checked.trans (by decide +kernel)
    · exact v3961_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 86 Primitive.Addresses.material3961
    · exact v3961_mb_checked.trans (by decide +kernel)
    · exact v3961_mg_checked.trans (by decide +kernel)
  upper_error := v3961_upper_checked
  lower_error := reuse_lower_error 57 86 Primitive.Addresses.material3961

def v3962_pa : Scalar.QComplex := ((999998198728171126452623820867 : Int)/10^30,(-1898035935689019892931946466 : Int)/10^30)
theorem v3962_pa_checked : Scalar.distance (sourceCoefficient 57 87 1 0) v3962_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3962_pb : Scalar.QComplex := ((-818959791350304465824336 : Int)/10^30,(-431476718002078967130948987 : Int)/10^30)
theorem v3962_pb_checked : Scalar.distance (sourceCoefficient 57 87 1 1) v3962_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3962_pg : Scalar.QComplex := ((-93086259441031628592162 : Int)/10^30,(176681383789148634842 : Int)/10^30)
theorem v3962_pg_checked : Scalar.distance (sourceCoefficient 57 87 1 2) v3962_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3962_mb : Scalar.QComplex := ((-1191304461059947667225271 : Int)/10^30,(-431475850618162039252858620 : Int)/10^30)
theorem v3962_mb_checked : Scalar.distance (sourceCoefficient 57 87 3 1) v3962_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3962_mg : Scalar.QComplex := ((-93086072312686210572060 : Int)/10^30,(257010567450710824138 : Int)/10^30)
theorem v3962_mg_checked : Scalar.distance (sourceCoefficient 57 87 3 2) v3962_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3962_upper : Scalar.QComplex := ((999993433510485636718920941978 : Int)/10^30,(-3623939280664346329052690238 : Int)/10^30)
theorem v3962_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 87 5) 1) 14) v3962_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3962 : Material (57 : Basis) (87 : Basis) where
  plus := ![v3962_pa,v3962_pb,v3962_pg]
  minus := ![(Primitive.Addresses.material3962 1).one,v3962_mb,v3962_mg]
  upper := v3962_upper
  lower := (Primitive.Addresses.material3962 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3962_pa_checked.trans (by decide +kernel)
    · exact v3962_pb_checked.trans (by decide +kernel)
    · exact v3962_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 87 Primitive.Addresses.material3962
    · exact v3962_mb_checked.trans (by decide +kernel)
    · exact v3962_mg_checked.trans (by decide +kernel)
  upper_error := v3962_upper_checked
  lower_error := reuse_lower_error 57 87 Primitive.Addresses.material3962

def v3963_pa : Scalar.QComplex := ((999998176338896073892693707047 : Int)/10^30,(-1909795507930729383512811912 : Int)/10^30)
theorem v3963_pa_checked : Scalar.distance (sourceCoefficient 57 88 1 0) v3963_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3963_pb : Scalar.QComplex := ((-824033780172533618926259 : Int)/10^30,(-431476707318796905765996720 : Int)/10^30)
theorem v3963_pb_checked : Scalar.distance (sourceCoefficient 57 88 1 1) v3963_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3963_pg : Scalar.QComplex := ((-93086257246563718328501 : Int)/10^30,(177776040142821313743 : Int)/10^30)
theorem v3963_pg_checked : Scalar.distance (sourceCoefficient 57 88 1 2) v3963_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3963_mb : Scalar.QComplex := ((-1196378438773707627271068 : Int)/10^30,(-431475835556260126151653337 : Int)/10^30)
theorem v3963_mb_checked : Scalar.distance (sourceCoefficient 57 88 3 1) v3963_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3963_mg : Scalar.QComplex := ((-93086069173579985681584 : Int)/10^30,(258105221503065942908 : Int)/10^30)
theorem v3963_mg_checked : Scalar.distance (sourceCoefficient 57 88 3 2) v3963_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3963_upper : Scalar.QComplex := ((999993390825289061223798782280 : Int)/10^30,(-3635698796749696740447120097 : Int)/10^30)
theorem v3963_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 88 5) 1) 14) v3963_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3963 : Material (57 : Basis) (88 : Basis) where
  plus := ![v3963_pa,v3963_pb,v3963_pg]
  minus := ![(Primitive.Addresses.material3963 1).one,v3963_mb,v3963_mg]
  upper := v3963_upper
  lower := (Primitive.Addresses.material3963 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3963_pa_checked.trans (by decide +kernel)
    · exact v3963_pb_checked.trans (by decide +kernel)
    · exact v3963_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 88 Primitive.Addresses.material3963
    · exact v3963_mb_checked.trans (by decide +kernel)
    · exact v3963_mg_checked.trans (by decide +kernel)
  upper_error := v3963_upper_checked
  lower_error := reuse_lower_error 57 88 Primitive.Addresses.material3963

def v3964_pa : Scalar.QComplex := ((999998145481835279755383403814 : Int)/10^30,(-1925884962868464258534928382 : Int)/10^30)
theorem v3964_pa_checked : Scalar.distance (sourceCoefficient 57 89 1 0) v3964_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3964_pb : Scalar.QComplex := ((-830976015114737292926114 : Int)/10^30,(-431476692573032682473750117 : Int)/10^30)
theorem v3964_pb_checked : Scalar.distance (sourceCoefficient 57 89 1 1) v3964_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3964_pg : Scalar.QComplex := ((-93086254219760382461394 : Int)/10^30,(179273749718012958142 : Int)/10^30)
theorem v3964_pg_checked : Scalar.distance (sourceCoefficient 57 89 1 2) v3964_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3964_mb : Scalar.QComplex := ((-1203320658406069556343838 : Int)/10^30,(-431475814819665304914636159 : Int)/10^30)
theorem v3964_mb_checked : Scalar.distance (sourceCoefficient 57 89 3 1) v3964_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3964_mg : Scalar.QComplex := ((-93086064854321867776545 : Int)/10^30,(259602927908596907063 : Int)/10^30)
theorem v3964_mg_checked : Scalar.distance (sourceCoefficient 57 89 3 2) v3964_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3964_upper : Scalar.QComplex := ((999993332199334626473416806013 : Int)/10^30,(-3651788174467590885862470592 : Int)/10^30)
theorem v3964_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 89 5) 1) 14) v3964_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3964 : Material (57 : Basis) (89 : Basis) where
  plus := ![v3964_pa,v3964_pb,v3964_pg]
  minus := ![(Primitive.Addresses.material3964 1).one,v3964_mb,v3964_mg]
  upper := v3964_upper
  lower := (Primitive.Addresses.material3964 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3964_pa_checked.trans (by decide +kernel)
    · exact v3964_pb_checked.trans (by decide +kernel)
    · exact v3964_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 89 Primitive.Addresses.material3964
    · exact v3964_mb_checked.trans (by decide +kernel)
    · exact v3964_mg_checked.trans (by decide +kernel)
  upper_error := v3964_upper_checked
  lower_error := reuse_lower_error 57 89 Primitive.Addresses.material3964

def v3965_pa : Scalar.QComplex := ((999998094674687478544515052818 : Int)/10^30,(-1952087855291960069037750902 : Int)/10^30)
theorem v3965_pa_checked : Scalar.distance (sourceCoefficient 57 90 1 0) v3965_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3965_pb : Scalar.QComplex := ((-842281968733653954974037 : Int)/10^30,(-431476668239670334146197790 : Int)/10^30)
theorem v3965_pb_checked : Scalar.distance (sourceCoefficient 57 90 1 1) v3965_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3965_pg : Scalar.QComplex := ((-93086249230207542216080 : Int)/10^30,(181712882839123994670 : Int)/10^30)
theorem v3965_pg_checked : Scalar.distance (sourceCoefficient 57 90 1 2) v3965_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3965_mb : Scalar.QComplex := ((-1214626586816667205813340 : Int)/10^30,(-431475780729783245133453508 : Int)/10^30)
theorem v3965_mb_checked : Scalar.distance (sourceCoefficient 57 90 3 1) v3965_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3965_mg : Scalar.QComplex := ((-93086057759908856328748 : Int)/10^30,(262042055815747828696 : Int)/10^30)
theorem v3965_mg_checked : Scalar.distance (sourceCoefficient 57 90 3 2) v3965_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3965_upper : Scalar.QComplex := ((999993236168447281418914797485 : Int)/10^30,(-3677990940176428523084176526 : Int)/10^30)
theorem v3965_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 90 5) 1) 14) v3965_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3965 : Material (57 : Basis) (90 : Basis) where
  plus := ![v3965_pa,v3965_pb,v3965_pg]
  minus := ![(Primitive.Addresses.material3965 1).one,v3965_mb,v3965_mg]
  upper := v3965_upper
  lower := (Primitive.Addresses.material3965 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3965_pa_checked.trans (by decide +kernel)
    · exact v3965_pb_checked.trans (by decide +kernel)
    · exact v3965_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 90 Primitive.Addresses.material3965
    · exact v3965_mb_checked.trans (by decide +kernel)
    · exact v3965_mg_checked.trans (by decide +kernel)
  upper_error := v3965_upper_checked
  lower_error := reuse_lower_error 57 90 Primitive.Addresses.material3965

def v3966_pa : Scalar.QComplex := ((999998065750835672282833379773 : Int)/10^30,(-1966848897941985941709305949 : Int)/10^30)
theorem v3966_pa_checked : Scalar.distance (sourceCoefficient 57 91 1 0) v3966_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3966_pb : Scalar.QComplex := ((-848651023613998701702205 : Int)/10^30,(-431476654357866784253825303 : Int)/10^30)
theorem v3966_pb_checked : Scalar.distance (sourceCoefficient 57 91 1 1) v3966_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3966_pg : Scalar.QComplex := ((-93086246386576874292567 : Int)/10^30,(183086935254746412087 : Int)/10^30)
theorem v3966_pg_checked : Scalar.distance (sourceCoefficient 57 91 1 2) v3966_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3966_mb : Scalar.QComplex := ((-1220995627346150490067239 : Int)/10^30,(-431475761351777353916835402 : Int)/10^30)
theorem v3966_mb_checked : Scalar.distance (sourceCoefficient 57 91 3 1) v3966_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3966_mg : Scalar.QComplex := ((-93086053730533897560266 : Int)/10^30,(263416105265822540433 : Int)/10^30)
theorem v3966_mg_checked : Scalar.distance (sourceCoefficient 57 91 3 2) v3966_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3966_upper : Scalar.QComplex := ((999993181768418051220854722840 : Int)/10^30,(-3692751910921671056146501003 : Int)/10^30)
theorem v3966_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 91 5) 1) 14) v3966_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3966 : Material (57 : Basis) (91 : Basis) where
  plus := ![v3966_pa,v3966_pb,v3966_pg]
  minus := ![(Primitive.Addresses.material3966 1).one,v3966_mb,v3966_mg]
  upper := v3966_upper
  lower := (Primitive.Addresses.material3966 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3966_pa_checked.trans (by decide +kernel)
    · exact v3966_pb_checked.trans (by decide +kernel)
    · exact v3966_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 91 Primitive.Addresses.material3966
    · exact v3966_mb_checked.trans (by decide +kernel)
    · exact v3966_mg_checked.trans (by decide +kernel)
  upper_error := v3966_upper_checked
  lower_error := reuse_lower_error 57 91 Primitive.Addresses.material3966

def v3967_pa : Scalar.QComplex := ((999998002387411167455248946042 : Int)/10^30,(-1998804939760014311298637587 : Int)/10^30)
theorem v3967_pa_checked : Scalar.distance (sourceCoefficient 57 92 1 0) v3967_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3967_pb : Scalar.QComplex := ((-862439330013677997412989 : Int)/10^30,(-431476623875846270683949737 : Int)/10^30)
theorem v3967_pb_checked : Scalar.distance (sourceCoefficient 57 92 1 1) v3967_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3967_pg : Scalar.QComplex := ((-93086240149362570954626 : Int)/10^30,(186061608313243944191 : Int)/10^30)
theorem v3967_pg_checked : Scalar.distance (sourceCoefficient 57 92 1 2) v3967_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3967_mb : Scalar.QComplex := ((-1234783902307202312474779 : Int)/10^30,(-431475718971080769540615780 : Int)/10^30)
theorem v3967_mb_checked : Scalar.distance (sourceCoefficient 57 92 3 1) v3967_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3967_mg : Scalar.QComplex := ((-93086044926313041440090 : Int)/10^30,(266390771834278313506 : Int)/10^30)
theorem v3967_mg_checked : Scalar.distance (sourceCoefficient 57 92 3 2) v3967_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3967_upper : Scalar.QComplex := ((999993063251858770321669726920 : Int)/10^30,(-3724707795785406547781549424 : Int)/10^30)
theorem v3967_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 92 5) 1) 14) v3967_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3967 : Material (57 : Basis) (92 : Basis) where
  plus := ![v3967_pa,v3967_pb,v3967_pg]
  minus := ![(Primitive.Addresses.material3967 1).one,v3967_mb,v3967_mg]
  upper := v3967_upper
  lower := (Primitive.Addresses.material3967 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3967_pa_checked.trans (by decide +kernel)
    · exact v3967_pb_checked.trans (by decide +kernel)
    · exact v3967_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 92 Primitive.Addresses.material3967
    · exact v3967_mb_checked.trans (by decide +kernel)
    · exact v3967_mg_checked.trans (by decide +kernel)
  upper_error := v3967_upper_checked
  lower_error := reuse_lower_error 57 92 Primitive.Addresses.material3967

def v3968_pa : Scalar.QComplex := ((999997925862336601570828267290 : Int)/10^30,(-2036730474252745012815590557 : Int)/10^30)
theorem v3968_pa_checked : Scalar.distance (sourceCoefficient 57 93 1 0) v3968_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3968_pb : Scalar.QComplex := ((-878803336300900950205868 : Int)/10^30,(-431476586937319450553927877 : Int)/10^30)
theorem v3968_pb_checked : Scalar.distance (sourceCoefficient 57 93 1 1) v3968_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3968_pg : Scalar.QComplex := ((-93086232603103392244108 : Int)/10^30,(189591959915944846195 : Int)/10^30)
theorem v3968_pg_checked : Scalar.distance (sourceCoefficient 57 93 1 2) v3968_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3968_mb : Scalar.QComplex := ((-1251147870625072856219797 : Int)/10^30,(-431475667911167284923067555 : Int)/10^30)
theorem v3968_mb_checked : Scalar.distance (sourceCoefficient 57 93 3 1) v3968_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3968_mg : Scalar.QComplex := ((-93086034333522240549652 : Int)/10^30,(269921115610386168456 : Int)/10^30)
theorem v3968_mg_checked : Scalar.distance (sourceCoefficient 57 93 3 2) v3968_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3968_upper : Scalar.QComplex := ((999992921270866222706220541312 : Int)/10^30,(-3762633141717172268425398877 : Int)/10^30)
theorem v3968_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 57 93 5) 1) 14) v3968_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3968 : Material (57 : Basis) (93 : Basis) where
  plus := ![v3968_pa,v3968_pb,v3968_pg]
  minus := ![(Primitive.Addresses.material3968 1).one,v3968_mb,v3968_mg]
  upper := v3968_upper
  lower := (Primitive.Addresses.material3968 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3968_pa_checked.trans (by decide +kernel)
    · exact v3968_pb_checked.trans (by decide +kernel)
    · exact v3968_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 57 93 Primitive.Addresses.material3968
    · exact v3968_mb_checked.trans (by decide +kernel)
    · exact v3968_mg_checked.trans (by decide +kernel)
  upper_error := v3968_upper_checked
  lower_error := reuse_lower_error 57 93 Primitive.Addresses.material3968

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
