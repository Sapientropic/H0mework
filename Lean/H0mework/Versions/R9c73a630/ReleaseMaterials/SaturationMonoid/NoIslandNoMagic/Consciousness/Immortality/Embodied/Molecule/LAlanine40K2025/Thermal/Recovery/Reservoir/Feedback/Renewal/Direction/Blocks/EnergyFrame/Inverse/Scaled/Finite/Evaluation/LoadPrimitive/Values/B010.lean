import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B006
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B007

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v161_pa : Scalar.QComplex := ((999975398774833784951986329853 : Int)/10^30,(7014402691045789767284507689 : Int)/10^30)
theorem v161_pa_checked : Scalar.distance (sourceCoefficient 1 66 1 0) v161_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v161_pb : Scalar.QComplex := ((3026519268830431512466090 : Int)/10^30,(-431461515121141567792889587 : Int)/10^30)
theorem v161_pb_checked : Scalar.distance (sourceCoefficient 1 66 1 1) v161_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v161_pg : Scalar.QComplex := ((-93083558331760380987093 : Int)/10^30,(-652941625218360152913 : Int)/10^30)
theorem v161_pg_checked : Scalar.distance (sourceCoefficient 1 66 1 2) v161_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v161_mb : Scalar.QComplex := ((2654186286674723766570327 : Int)/10^30,(-431463966218120355659930181 : Int)/10^30)
theorem v161_mb_checked : Scalar.distance (sourceCoefficient 1 66 3 1) v161_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v161_mg : Scalar.QComplex := ((-93084087131712649597663 : Int)/10^30,(-572614463585883706633 : Int)/10^30)
theorem v161_mg_checked : Scalar.distance (sourceCoefficient 1 66 3 2) v161_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v161_upper : Scalar.QComplex := ((999986015651645775398350786626 : Int)/10^30,(5288525422691122035569216054 : Int)/10^30)
theorem v161_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 66 5) 1) 14) v161_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material161 : Material (1 : Basis) (66 : Basis) where
  plus := ![v161_pa,v161_pb,v161_pg]
  minus := ![(Primitive.Addresses.material161 1).one,v161_mb,v161_mg]
  upper := v161_upper
  lower := (Primitive.Addresses.material161 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v161_pa_checked.trans (by decide +kernel)
    · exact v161_pb_checked.trans (by decide +kernel)
    · exact v161_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 66 Primitive.Addresses.material161
    · exact v161_mb_checked.trans (by decide +kernel)
    · exact v161_mg_checked.trans (by decide +kernel)
  upper_error := v161_upper_checked
  lower_error := reuse_lower_error 1 66 Primitive.Addresses.material161

def v162_pa : Scalar.QComplex := ((999975605384424700055802832583 : Int)/10^30,(6984886259154892045943868717 : Int)/10^30)
theorem v162_pa_checked : Scalar.distance (sourceCoefficient 1 67 1 0) v162_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v162_pb : Scalar.QComplex := ((3013783493912060443858900 : Int)/10^30,(-431461567448190756558523765 : Int)/10^30)
theorem v162_pb_checked : Scalar.distance (sourceCoefficient 1 67 1 1) v162_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v162_pg : Scalar.QComplex := ((-93083573592511688374464 : Int)/10^30,(-650194035372910337703 : Int)/10^30)
theorem v162_pg_checked : Scalar.distance (sourceCoefficient 1 67 1 2) v162_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v162_mb : Scalar.QComplex := ((2641450471342577026645547 : Int)/10^30,(-431464007554749904128819326 : Int)/10^30)
theorem v162_mb_checked : Scalar.distance (sourceCoefficient 1 67 3 1) v162_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v162_mg : Scalar.QComplex := ((-93084100021411984939621 : Int)/10^30,(-569866861594146102392 : Int)/10^30)
theorem v162_mg_checked : Scalar.distance (sourceCoefficient 1 67 3 2) v162_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v162_upper : Scalar.QComplex := ((999986171318245235881120942867 : Int)/10^30,(5259008678172071928272879943 : Int)/10^30)
theorem v162_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 67 5) 1) 14) v162_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material162 : Material (1 : Basis) (67 : Basis) where
  plus := ![v162_pa,v162_pb,v162_pg]
  minus := ![(Primitive.Addresses.material162 1).one,v162_mb,v162_mg]
  upper := v162_upper
  lower := (Primitive.Addresses.material162 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v162_pa_checked.trans (by decide +kernel)
    · exact v162_pb_checked.trans (by decide +kernel)
    · exact v162_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 67 Primitive.Addresses.material162
    · exact v162_mb_checked.trans (by decide +kernel)
    · exact v162_mg_checked.trans (by decide +kernel)
  upper_error := v162_upper_checked
  lower_error := reuse_lower_error 1 67 Primitive.Addresses.material162

def v163_pa : Scalar.QComplex := ((999975947539120833992879793145 : Int)/10^30,(6935729466859103958053911235 : Int)/10^30)
theorem v163_pa_checked : Scalar.distance (sourceCoefficient 1 68 1 0) v163_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v163_pb : Scalar.QComplex := ((2992573282622319755165679 : Int)/10^30,(-431461653481373119948394272 : Int)/10^30)
theorem v163_pb_checked : Scalar.distance (sourceCoefficient 1 68 1 1) v163_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v163_pg : Scalar.QComplex := ((-93083598797820999918156 : Int)/10^30,(-645618187769541978845 : Int)/10^30)
theorem v163_pg_checked : Scalar.distance (sourceCoefficient 1 68 1 2) v163_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v163_mb : Scalar.QComplex := ((2620240193707605766755008 : Int)/10^30,(-431464075284443162841880437 : Int)/10^30)
theorem v163_mb_checked : Scalar.distance (sourceCoefficient 1 68 3 1) v163_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v163_mg : Scalar.QComplex := ((-93084121277961518213513 : Int)/10^30,(-565290993943528201964 : Int)/10^30)
theorem v163_mg_checked : Scalar.distance (sourceCoefficient 1 68 3 2) v163_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v163_upper : Scalar.QComplex := ((999986428632267737421991626637 : Int)/10^30,(5209851368561586106895833307 : Int)/10^30)
theorem v163_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 68 5) 1) 14) v163_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material163 : Material (1 : Basis) (68 : Basis) where
  plus := ![v163_pa,v163_pb,v163_pg]
  minus := ![(Primitive.Addresses.material163 1).one,v163_mb,v163_mg]
  upper := v163_upper
  lower := (Primitive.Addresses.material163 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v163_pa_checked.trans (by decide +kernel)
    · exact v163_pb_checked.trans (by decide +kernel)
    · exact v163_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 68 Primitive.Addresses.material163
    · exact v163_mb_checked.trans (by decide +kernel)
    · exact v163_mg_checked.trans (by decide +kernel)
  upper_error := v163_upper_checked
  lower_error := reuse_lower_error 1 68 Primitive.Addresses.material163

def v164_pa : Scalar.QComplex := ((999976097362277921546659007330 : Int)/10^30,(6914094597853491457113197544 : Int)/10^30)
theorem v164_pa_checked : Scalar.distance (sourceCoefficient 1 69 1 0) v164_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v164_pb : Scalar.QComplex := ((2983238253534910476206934 : Int)/10^30,(-431461690905680375080254335 : Int)/10^30)
theorem v164_pb_checked : Scalar.distance (sourceCoefficient 1 69 1 1) v164_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v164_pg : Scalar.QComplex := ((-93083609808001959602856 : Int)/10^30,(-643604267561852536634 : Int)/10^30)
theorem v164_pg_checked : Scalar.distance (sourceCoefficient 1 69 1 2) v164_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v164_mb : Scalar.QComplex := ((2610905135800562815994303 : Int)/10^30,(-431464104653026814862415728 : Int)/10^30)
theorem v164_mb_checked : Scalar.distance (sourceCoefficient 1 69 3 1) v164_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v164_mg : Scalar.QComplex := ((-93084130550215942667742 : Int)/10^30,(-563277064984423005711 : Int)/10^30)
theorem v164_mg_checked : Scalar.distance (sourceCoefficient 1 69 3 2) v164_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v164_upper : Scalar.QComplex := ((999986541115380477279994902971 : Int)/10^30,(5188216273197392297096657723 : Int)/10^30)
theorem v164_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 69 5) 1) 14) v164_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material164 : Material (1 : Basis) (69 : Basis) where
  plus := ![v164_pa,v164_pb,v164_pg]
  minus := ![(Primitive.Addresses.material164 1).one,v164_mb,v164_mg]
  upper := v164_upper
  lower := (Primitive.Addresses.material164 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v164_pa_checked.trans (by decide +kernel)
    · exact v164_pb_checked.trans (by decide +kernel)
    · exact v164_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 69 Primitive.Addresses.material164
    · exact v164_mb_checked.trans (by decide +kernel)
    · exact v164_mg_checked.trans (by decide +kernel)
  upper_error := v164_upper_checked
  lower_error := reuse_lower_error 1 69 Primitive.Addresses.material164

def v165_pa : Scalar.QComplex := ((999976195662166283292960611313 : Int)/10^30,(6899862971170783501864078640 : Int)/10^30)
theorem v165_pa_checked : Scalar.distance (sourceCoefficient 1 70 1 0) v165_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v165_pb : Scalar.QComplex := ((2977097581243594443106386 : Int)/10^30,(-431461715376915423244113263 : Int)/10^30)
theorem v165_pb_checked : Scalar.distance (sourceCoefficient 1 70 1 1) v165_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v165_pg : Scalar.QComplex := ((-93083617022886935140037 : Int)/10^30,(-642279491356855895701 : Int)/10^30)
theorem v165_pg_checked : Scalar.distance (sourceCoefficient 1 70 1 2) v165_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v165_mb : Scalar.QComplex := ((2604764444678126016486121 : Int)/10^30,(-431464123825129129474741687 : Int)/10^30)
theorem v165_mb_checked : Scalar.distance (sourceCoefficient 1 70 3 1) v165_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v165_mg : Scalar.QComplex := ((-93084136621876032566787 : Int)/10^30,(-561952283046580303630 : Int)/10^30)
theorem v165_mg_checked : Scalar.distance (sourceCoefficient 1 70 3 2) v165_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v165_upper : Scalar.QComplex := ((999986614852625861623034611301 : Int)/10^30,(5173984498054330905272691081 : Int)/10^30)
theorem v165_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 70 5) 1) 14) v165_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material165 : Material (1 : Basis) (70 : Basis) where
  plus := ![v165_pa,v165_pb,v165_pg]
  minus := ![(Primitive.Addresses.material165 1).one,v165_mb,v165_mg]
  upper := v165_upper
  lower := (Primitive.Addresses.material165 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v165_pa_checked.trans (by decide +kernel)
    · exact v165_pb_checked.trans (by decide +kernel)
    · exact v165_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 70 Primitive.Addresses.material165
    · exact v165_mb_checked.trans (by decide +kernel)
    · exact v165_mg_checked.trans (by decide +kernel)
  upper_error := v165_upper_checked
  lower_error := reuse_lower_error 1 70 Primitive.Addresses.material165

def v166_pa : Scalar.QComplex := ((999976362984207908581106783685 : Int)/10^30,(6875570730904255791612519889 : Int)/10^30)
theorem v166_pa_checked : Scalar.distance (sourceCoefficient 1 71 1 0) v166_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v166_pb : Scalar.QComplex := ((2966615949043855699367381 : Int)/10^30,(-431461756878132978927525781 : Int)/10^30)
theorem v166_pb_checked : Scalar.distance (sourceCoefficient 1 71 1 1) v166_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v166_pg : Scalar.QComplex := ((-93083629287295022910965 : Int)/10^30,(-640018205174490766733 : Int)/10^30)
theorem v166_pg_checked : Scalar.distance (sourceCoefficient 1 71 1 2) v166_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v166_mb : Scalar.QComplex := ((2594282780567496369864133 : Int)/10^30,(-431464156281154719173644480 : Int)/10^30)
theorem v166_mb_checked : Scalar.distance (sourceCoefficient 1 71 3 1) v166_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v166_mg : Scalar.QComplex := ((-93084146934891422905972 : Int)/10^30,(-559690987122563554929 : Int)/10^30)
theorem v166_mg_checked : Scalar.distance (sourceCoefficient 1 71 3 2) v166_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v166_upper : Scalar.QComplex := ((999986740248215355180414935062 : Int)/10^30,(5149692005185576996814734097 : Int)/10^30)
theorem v166_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 71 5) 1) 14) v166_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material166 : Material (1 : Basis) (71 : Basis) where
  plus := ![v166_pa,v166_pb,v166_pg]
  minus := ![(Primitive.Addresses.material166 1).one,v166_mb,v166_mg]
  upper := v166_upper
  lower := (Primitive.Addresses.material166 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v166_pa_checked.trans (by decide +kernel)
    · exact v166_pb_checked.trans (by decide +kernel)
    · exact v166_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 71 Primitive.Addresses.material166
    · exact v166_mb_checked.trans (by decide +kernel)
    · exact v166_mg_checked.trans (by decide +kernel)
  upper_error := v166_upper_checked
  lower_error := reuse_lower_error 1 71 Primitive.Addresses.material166

def v167_pa : Scalar.QComplex := ((999976543894822972395475309027 : Int)/10^30,(6849208725479545003423835968 : Int)/10^30)
theorem v167_pa_checked : Scalar.distance (sourceCoefficient 1 72 1 0) v167_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v167_pb : Scalar.QComplex := ((2955241254208506476775561 : Int)/10^30,(-431461801531230006424307920 : Int)/10^30)
theorem v167_pb_checked : Scalar.distance (sourceCoefficient 1 72 1 1) v167_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v167_pg : Scalar.QComplex := ((-93083642524149502951654 : Int)/10^30,(-637564251349960372028 : Int)/10^30)
theorem v167_pg_checked : Scalar.distance (sourceCoefficient 1 72 1 2) v167_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v167_mb : Scalar.QComplex := ((2582908051433854249812701 : Int)/10^30,(-431464191118385774613293571 : Int)/10^30)
theorem v167_mb_checked : Scalar.distance (sourceCoefficient 1 72 3 1) v167_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v167_mg : Scalar.QComplex := ((-93084158054089345668542 : Int)/10^30,(-557237022788943069847 : Int)/10^30)
theorem v167_mg_checked : Scalar.distance (sourceCoefficient 1 72 3 2) v167_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v167_upper : Scalar.QComplex := ((999986875660131153284504521643 : Int)/10^30,(5123329726788667072695198282 : Int)/10^30)
theorem v167_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 72 5) 1) 14) v167_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material167 : Material (1 : Basis) (72 : Basis) where
  plus := ![v167_pa,v167_pb,v167_pg]
  minus := ![(Primitive.Addresses.material167 1).one,v167_mb,v167_mg]
  upper := v167_upper
  lower := (Primitive.Addresses.material167 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v167_pa_checked.trans (by decide +kernel)
    · exact v167_pb_checked.trans (by decide +kernel)
    · exact v167_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 72 Primitive.Addresses.material167
    · exact v167_mb_checked.trans (by decide +kernel)
    · exact v167_mg_checked.trans (by decide +kernel)
  upper_error := v167_upper_checked
  lower_error := reuse_lower_error 1 72 Primitive.Addresses.material167

def v168_pa : Scalar.QComplex := ((999976608572750901398052782116 : Int)/10^30,(6839759304195466644874862598 : Int)/10^30)
theorem v168_pa_checked : Scalar.distance (sourceCoefficient 1 73 1 0) v168_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v168_pb : Scalar.QComplex := ((2951164012176697688178084 : Int)/10^30,(-431461817439719411676962042 : Int)/10^30)
theorem v168_pb_checked : Scalar.distance (sourceCoefficient 1 73 1 1) v168_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v168_pg : Scalar.QComplex := ((-93083647250503827284772 : Int)/10^30,(-636684635312409848689 : Int)/10^30)
theorem v168_pg_checked : Scalar.distance (sourceCoefficient 1 73 1 2) v168_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v168_mb : Scalar.QComplex := ((2578830797191879143856178 : Int)/10^30,(-431464203508393015121669978 : Int)/10^30)
theorem v168_mb_checked : Scalar.distance (sourceCoefficient 1 73 3 1) v168_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v168_mg : Scalar.QComplex := ((-93084162021372886193539 : Int)/10^30,(-556357403000282882924 : Int)/10^30)
theorem v168_mg_checked : Scalar.distance (sourceCoefficient 1 73 3 2) v168_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v168_upper : Scalar.QComplex := ((999986924029118860594250688010 : Int)/10^30,(5113880207950155640111769497 : Int)/10^30)
theorem v168_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 73 5) 1) 14) v168_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material168 : Material (1 : Basis) (73 : Basis) where
  plus := ![v168_pa,v168_pb,v168_pg]
  minus := ![(Primitive.Addresses.material168 1).one,v168_mb,v168_mg]
  upper := v168_upper
  lower := (Primitive.Addresses.material168 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v168_pa_checked.trans (by decide +kernel)
    · exact v168_pb_checked.trans (by decide +kernel)
    · exact v168_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 73 Primitive.Addresses.material168
    · exact v168_mb_checked.trans (by decide +kernel)
    · exact v168_mg_checked.trans (by decide +kernel)
  upper_error := v168_upper_checked
  lower_error := reuse_lower_error 1 73 Primitive.Addresses.material168

def v169_pa : Scalar.QComplex := ((999976681244548563537674200689 : Int)/10^30,(6829126381794169194350866557 : Int)/10^30)
theorem v169_pa_checked : Scalar.distance (sourceCoefficient 1 74 1 0) v169_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v169_pb : Scalar.QComplex := ((2946576112530675290715340 : Int)/10^30,(-431461835279254651921657627 : Int)/10^30)
theorem v169_pb_checked : Scalar.distance (sourceCoefficient 1 74 1 1) v169_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v169_pg : Scalar.QComplex := ((-93083652557218843491398 : Int)/10^30,(-635694851005037809251 : Int)/10^30)
theorem v169_pg_checked : Scalar.distance (sourceCoefficient 1 74 1 2) v169_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v169_mb : Scalar.QComplex := ((2574242883859426012489774 : Int)/10^30,(-431464217388770849704300912 : Int)/10^30)
theorem v169_mb_checked : Scalar.distance (sourceCoefficient 1 74 3 1) v169_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v169_mg : Scalar.QComplex := ((-93084166473946647435947 : Int)/10^30,(-555367614481996723084 : Int)/10^30)
theorem v169_mg_checked : Scalar.distance (sourceCoefficient 1 74 3 2) v169_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v169_upper : Scalar.QComplex := ((999986978349348833173600406418 : Int)/10^30,(5103247175960417044646752087 : Int)/10^30)
theorem v169_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 74 5) 1) 14) v169_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material169 : Material (1 : Basis) (74 : Basis) where
  plus := ![v169_pa,v169_pb,v169_pg]
  minus := ![(Primitive.Addresses.material169 1).one,v169_mb,v169_mg]
  upper := v169_upper
  lower := (Primitive.Addresses.material169 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v169_pa_checked.trans (by decide +kernel)
    · exact v169_pb_checked.trans (by decide +kernel)
    · exact v169_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 74 Primitive.Addresses.material169
    · exact v169_mb_checked.trans (by decide +kernel)
    · exact v169_mg_checked.trans (by decide +kernel)
  upper_error := v169_upper_checked
  lower_error := reuse_lower_error 1 74 Primitive.Addresses.material169

def v170_pa : Scalar.QComplex := ((999976782309194998732788636358 : Int)/10^30,(6814311597574344690698618135 : Int)/10^30)
theorem v170_pa_checked : Scalar.distance (sourceCoefficient 1 75 1 0) v170_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v170_pb : Scalar.QComplex := ((2940183820968550466324131 : Int)/10^30,(-431461860026515826316528949 : Int)/10^30)
theorem v170_pb_checked : Scalar.distance (sourceCoefficient 1 75 1 1) v170_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v170_pg : Scalar.QComplex := ((-93083659930558962611517 : Int)/10^30,(-634315790757376794143 : Int)/10^30)
theorem v170_pg_checked : Scalar.distance (sourceCoefficient 1 75 1 2) v170_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v170_mb : Scalar.QComplex := ((2567850573321671660599684 : Int)/10^30,(-431464236619763089573785203 : Int)/10^30)
theorem v170_mb_checked : Scalar.distance (sourceCoefficient 1 75 3 1) v170_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v170_mg : Scalar.QComplex := ((-93084172657217137961007 : Int)/10^30,(-553988548384962424457 : Int)/10^30)
theorem v170_mg_checked : Scalar.distance (sourceCoefficient 1 75 3 2) v170_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v170_upper : Scalar.QComplex := ((999987053844871167758417966203 : Int)/10^30,(5088432239377062135578905432 : Int)/10^30)
theorem v170_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 75 5) 1) 14) v170_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material170 : Material (1 : Basis) (75 : Basis) where
  plus := ![v170_pa,v170_pb,v170_pg]
  minus := ![(Primitive.Addresses.material170 1).one,v170_mb,v170_mg]
  upper := v170_upper
  lower := (Primitive.Addresses.material170 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v170_pa_checked.trans (by decide +kernel)
    · exact v170_pb_checked.trans (by decide +kernel)
    · exact v170_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 75 Primitive.Addresses.material170
    · exact v170_mb_checked.trans (by decide +kernel)
    · exact v170_mg_checked.trans (by decide +kernel)
  upper_error := v170_upper_checked
  lower_error := reuse_lower_error 1 75 Primitive.Addresses.material170

def v171_pa : Scalar.QComplex := ((999976866935095630268735201779 : Int)/10^30,(6801881700680157576584279569 : Int)/10^30)
theorem v171_pa_checked : Scalar.distance (sourceCoefficient 1 76 1 0) v171_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v171_pb : Scalar.QComplex := ((2934820562218173875699404 : Int)/10^30,(-431461880692538850926748349 : Int)/10^30)
theorem v171_pb_checked : Scalar.distance (sourceCoefficient 1 76 1 1) v171_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v171_pg : Scalar.QComplex := ((-93083666098547183529135 : Int)/10^30,(-633158731969971474775 : Int)/10^30)
theorem v171_pg_checked : Scalar.distance (sourceCoefficient 1 76 1 2) v171_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v171_mb : Scalar.QComplex := ((2562487298734434308660741 : Int)/10^30,(-431464252657527669911428458 : Int)/10^30)
theorem v171_mb_checked : Scalar.distance (sourceCoefficient 1 76 3 1) v171_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v171_mg : Scalar.QComplex := ((-93084177826713440717226 : Int)/10^30,(-552831484705686933065 : Int)/10^30)
theorem v171_mg_checked : Scalar.distance (sourceCoefficient 1 76 3 2) v171_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v171_upper : Scalar.QComplex := ((999987117017771351026938757025 : Int)/10^30,(5076002214939119038802609102 : Int)/10^30)
theorem v171_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 76 5) 1) 14) v171_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material171 : Material (1 : Basis) (76 : Basis) where
  plus := ![v171_pa,v171_pb,v171_pg]
  minus := ![(Primitive.Addresses.material171 1).one,v171_mb,v171_mg]
  upper := v171_upper
  lower := (Primitive.Addresses.material171 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v171_pa_checked.trans (by decide +kernel)
    · exact v171_pb_checked.trans (by decide +kernel)
    · exact v171_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 76 Primitive.Addresses.material171
    · exact v171_mb_checked.trans (by decide +kernel)
    · exact v171_mg_checked.trans (by decide +kernel)
  upper_error := v171_upper_checked
  lower_error := reuse_lower_error 1 76 Primitive.Addresses.material171

def v172_pa : Scalar.QComplex := ((999976886504685461393137660241 : Int)/10^30,(6799004073789892834420913744 : Int)/10^30)
theorem v172_pa_checked : Scalar.distance (sourceCoefficient 1 77 1 0) v172_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v172_pb : Scalar.QComplex := ((2933578922219023944705789 : Int)/10^30,(-431461885464227424419384099 : Int)/10^30)
theorem v172_pb_checked : Scalar.distance (sourceCoefficient 1 77 1 1) v172_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v172_pg : Scalar.QComplex := ((-93083667524096886934593 : Int)/10^30,(-632890863019635700539 : Int)/10^30)
theorem v172_pg_checked : Scalar.distance (sourceCoefficient 1 77 1 2) v172_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v172_mb : Scalar.QComplex := ((2561245655079851365053316 : Int)/10^30,(-431464256357735068809603058 : Int)/10^30)
theorem v172_mb_checked : Scalar.distance (sourceCoefficient 1 77 3 1) v172_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v172_mg : Scalar.QComplex := ((-93084179021103773555278 : Int)/10^30,(-552563614624905821591 : Int)/10^30)
theorem v172_mg_checked : Scalar.distance (sourceCoefficient 1 77 3 2) v172_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v172_upper : Scalar.QComplex := ((999987131620809079221373415640 : Int)/10^30,(5073124558559404810689319147 : Int)/10^30)
theorem v172_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 77 5) 1) 14) v172_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material172 : Material (1 : Basis) (77 : Basis) where
  plus := ![v172_pa,v172_pb,v172_pg]
  minus := ![(Primitive.Addresses.material172 1).one,v172_mb,v172_mg]
  upper := v172_upper
  lower := (Primitive.Addresses.material172 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v172_pa_checked.trans (by decide +kernel)
    · exact v172_pb_checked.trans (by decide +kernel)
    · exact v172_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 77 Primitive.Addresses.material172
    · exact v172_mb_checked.trans (by decide +kernel)
    · exact v172_mg_checked.trans (by decide +kernel)
  upper_error := v172_upper_checked
  lower_error := reuse_lower_error 1 77 Primitive.Addresses.material172

def v173_pa : Scalar.QComplex := ((999977003975028825319344216727 : Int)/10^30,(6781704883374451765490813870 : Int)/10^30)
theorem v173_pa_checked : Scalar.distance (sourceCoefficient 1 78 1 0) v173_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v173_pb : Scalar.QComplex := ((2926114658504541635241054 : Int)/10^30,(-431461914049382627650184773 : Int)/10^30)
theorem v173_pb_checked : Scalar.distance (sourceCoefficient 1 78 1 1) v173_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v173_pg : Scalar.QComplex := ((-93083676075001200378707 : Int)/10^30,(-631280537543286423674 : Int)/10^30)
theorem v173_pg_checked : Scalar.distance (sourceCoefficient 1 78 1 2) v173_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v173_mb : Scalar.QComplex := ((2553781369476954057405058 : Int)/10^30,(-431464278501556220840670242 : Int)/10^30)
theorem v173_mb_checked : Scalar.distance (sourceCoefficient 1 78 3 1) v173_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v173_mg : Scalar.QComplex := ((-93084186182366543384645 : Int)/10^30,(-550953282369109011012 : Int)/10^30)
theorem v173_mg_checked : Scalar.distance (sourceCoefficient 1 78 3 2) v173_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v173_upper : Scalar.QComplex := ((999987219234144198114131126775 : Int)/10^30,(5055825191165919940071641447 : Int)/10^30)
theorem v173_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 78 5) 1) 14) v173_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material173 : Material (1 : Basis) (78 : Basis) where
  plus := ![v173_pa,v173_pb,v173_pg]
  minus := ![(Primitive.Addresses.material173 1).one,v173_mb,v173_mg]
  upper := v173_upper
  lower := (Primitive.Addresses.material173 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v173_pa_checked.trans (by decide +kernel)
    · exact v173_pb_checked.trans (by decide +kernel)
    · exact v173_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 78 Primitive.Addresses.material173
    · exact v173_mb_checked.trans (by decide +kernel)
    · exact v173_mg_checked.trans (by decide +kernel)
  upper_error := v173_upper_checked
  lower_error := reuse_lower_error 1 78 Primitive.Addresses.material173

def v174_pa : Scalar.QComplex := ((999977041781595192904898053963 : Int)/10^30,(6776127930449798361499595546 : Int)/10^30)
theorem v174_pa_checked : Scalar.distance (sourceCoefficient 1 79 1 0) v174_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v174_pb : Scalar.QComplex := ((2923708312045023795464973 : Int)/10^30,(-431461923228030473414734444 : Int)/10^30)
theorem v174_pb_checked : Scalar.distance (sourceCoefficient 1 79 1 1) v174_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v174_pg : Scalar.QComplex := ((-93083678824733424151587 : Int)/10^30,(-630761397111210816853 : Int)/10^30)
theorem v174_pg_checked : Scalar.distance (sourceCoefficient 1 79 1 2) v174_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v174_mb : Scalar.QComplex := ((2551375015992669280031940 : Int)/10^30,(-431464285603632032232609122 : Int)/10^30)
theorem v174_mb_checked : Scalar.distance (sourceCoefficient 1 79 3 1) v174_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v174_mg : Scalar.QComplex := ((-93084188484102931642409 : Int)/10^30,(-550434139757438047169 : Int)/10^30)
theorem v174_mg_checked : Scalar.distance (sourceCoefficient 1 79 3 2) v174_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v174_upper : Scalar.QComplex := ((999987247415339446525536315058 : Int)/10^30,(5050248181296779036898018157 : Int)/10^30)
theorem v174_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 79 5) 1) 14) v174_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material174 : Material (1 : Basis) (79 : Basis) where
  plus := ![v174_pa,v174_pb,v174_pg]
  minus := ![(Primitive.Addresses.material174 1).one,v174_mb,v174_mg]
  upper := v174_upper
  lower := (Primitive.Addresses.material174 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v174_pa_checked.trans (by decide +kernel)
    · exact v174_pb_checked.trans (by decide +kernel)
    · exact v174_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 79 Primitive.Addresses.material174
    · exact v174_mb_checked.trans (by decide +kernel)
    · exact v174_mg_checked.trans (by decide +kernel)
  upper_error := v174_upper_checked
  lower_error := reuse_lower_error 1 79 Primitive.Addresses.material174

def v175_pa : Scalar.QComplex := ((999977100776947464737210749720 : Int)/10^30,(6767416178324938500626986711 : Int)/10^30)
theorem v175_pa_checked : Scalar.distance (sourceCoefficient 1 80 1 0) v175_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v175_pb : Scalar.QComplex := ((2919949360944865723948109 : Int)/10^30,(-431461937530177524810047528 : Int)/10^30)
theorem v175_pb_checked : Scalar.distance (sourceCoefficient 1 80 1 1) v175_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v175_pg : Scalar.QComplex := ((-93083683113327430378920 : Int)/10^30,(-629950448415034232659 : Int)/10^30)
theorem v175_pg_checked : Scalar.distance (sourceCoefficient 1 80 1 2) v175_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v175_mb : Scalar.QComplex := ((2547616053950031735093188 : Int)/10^30,(-431464296661968255721474627 : Int)/10^30)
theorem v175_mb_checked : Scalar.distance (sourceCoefficient 1 80 3 1) v175_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v175_mg : Scalar.QComplex := ((-93084192072883140003252 : Int)/10^30,(-549623187662351248478 : Int)/10^30)
theorem v175_mg_checked : Scalar.distance (sourceCoefficient 1 80 3 2) v175_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v175_upper : Scalar.QComplex := ((999987291374910008181696303023 : Int)/10^30,(5041536340326424607080737856 : Int)/10^30)
theorem v175_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 80 5) 1) 14) v175_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material175 : Material (1 : Basis) (80 : Basis) where
  plus := ![v175_pa,v175_pb,v175_pg]
  minus := ![(Primitive.Addresses.material175 1).one,v175_mb,v175_mg]
  upper := v175_upper
  lower := (Primitive.Addresses.material175 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v175_pa_checked.trans (by decide +kernel)
    · exact v175_pb_checked.trans (by decide +kernel)
    · exact v175_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 80 Primitive.Addresses.material175
    · exact v175_mb_checked.trans (by decide +kernel)
    · exact v175_mg_checked.trans (by decide +kernel)
  upper_error := v175_upper_checked
  lower_error := reuse_lower_error 1 80 Primitive.Addresses.material175

def v176_pa : Scalar.QComplex := ((999977277956697552307260692376 : Int)/10^30,(6741184637260987169983689717 : Int)/10^30)
theorem v176_pa_checked : Scalar.distance (sourceCoefficient 1 81 1 0) v176_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v176_pb : Scalar.QComplex := ((2908630963408300450065717 : Int)/10^30,(-431461980331008845695005160 : Int)/10^30)
theorem v176_pb_checked : Scalar.distance (sourceCoefficient 1 81 1 1) v176_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v176_pg : Scalar.QComplex := ((-93083695976732397469738 : Int)/10^30,(-627508639576301910442 : Int)/10^30)
theorem v176_pg_checked : Scalar.distance (sourceCoefficient 1 81 1 2) v176_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v176_mb : Scalar.QComplex := ((2536297623692633388355645 : Int)/10^30,(-431464329695516327546808543 : Int)/10^30)
theorem v176_mb_checked : Scalar.distance (sourceCoefficient 1 81 3 1) v176_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v176_mg : Scalar.QComplex := ((-93084202829112264622154 : Int)/10^30,(-547181368632276812751 : Int)/10^30)
theorem v176_mg_checked : Scalar.distance (sourceCoefficient 1 81 3 2) v176_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v176_upper : Scalar.QComplex := ((999987423281136037763061763902 : Int)/10^30,(5015304532535097288146708385 : Int)/10^30)
theorem v176_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 1 81 5) 1) 14) v176_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material176 : Material (1 : Basis) (81 : Basis) where
  plus := ![v176_pa,v176_pb,v176_pg]
  minus := ![(Primitive.Addresses.material176 1).one,v176_mb,v176_mg]
  upper := v176_upper
  lower := (Primitive.Addresses.material176 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v176_pa_checked.trans (by decide +kernel)
    · exact v176_pb_checked.trans (by decide +kernel)
    · exact v176_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 1 81 Primitive.Addresses.material176
    · exact v176_mb_checked.trans (by decide +kernel)
    · exact v176_mg_checked.trans (by decide +kernel)
  upper_error := v176_upper_checked
  lower_error := reuse_lower_error 1 81 Primitive.Addresses.material176

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
