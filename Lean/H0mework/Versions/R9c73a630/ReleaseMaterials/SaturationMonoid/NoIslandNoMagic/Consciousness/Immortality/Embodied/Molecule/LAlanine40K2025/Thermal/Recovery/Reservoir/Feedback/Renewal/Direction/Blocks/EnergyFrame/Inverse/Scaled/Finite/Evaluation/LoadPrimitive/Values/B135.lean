import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B090

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2161_pa : Scalar.QComplex := ((999999546508278294406728854805 : Int)/10^30,(-952356675703197287556497048 : Int)/10^30)
theorem v2161_pa_checked : Scalar.distance (sourceCoefficient 25 62 1 0) v2161_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2161_pb : Scalar.QComplex := ((-410920482795466144037537 : Int)/10^30,(-431477309846140620689193765 : Int)/10^30)
theorem v2161_pb_checked : Scalar.distance (sourceCoefficient 25 62 1 1) v2161_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2161_pg : Scalar.QComplex := ((-93086386012905966806041 : Int)/10^30,(88651481339188632048 : Int)/10^30)
theorem v2161_pg_checked : Scalar.distance (sourceCoefficient 25 62 1 2) v2161_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2161_mb : Scalar.QComplex := ((-783265815171561778040081 : Int)/10^30,(-431476794581549196787963334 : Int)/10^30)
theorem v2161_mb_checked : Scalar.distance (sourceCoefficient 25 62 3 1) v2161_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2161_mg : Scalar.QComplex := ((-93086274850354514978949 : Int)/10^30,(168980807004133637028 : Int)/10^30)
theorem v2161_mg_checked : Scalar.distance (sourceCoefficient 25 62 3 2) v2161_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2161_upper : Scalar.QComplex := ((999996413445196827753941798334 : Int)/10^30,(-2678263755302889498910260581 : Int)/10^30)
theorem v2161_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 62 5) 1) 14) v2161_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2161 : Material (25 : Basis) (62 : Basis) where
  plus := ![v2161_pa,v2161_pb,v2161_pg]
  minus := ![(Primitive.Addresses.material2161 1).one,v2161_mb,v2161_mg]
  upper := v2161_upper
  lower := (Primitive.Addresses.material2161 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2161_pa_checked.trans (by decide +kernel)
    · exact v2161_pb_checked.trans (by decide +kernel)
    · exact v2161_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 62 Primitive.Addresses.material2161
    · exact v2161_mb_checked.trans (by decide +kernel)
    · exact v2161_mg_checked.trans (by decide +kernel)
  upper_error := v2161_upper_checked
  lower_error := reuse_lower_error 25 62 Primitive.Addresses.material2161

def v2162_pa : Scalar.QComplex := ((999999522587028794180650475642 : Int)/10^30,(-977151837990643920520432821 : Int)/10^30)
theorem v2162_pa_checked : Scalar.distance (sourceCoefficient 25 63 1 0) v2162_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2162_pb : Scalar.QComplex := ((-421619035908028054593932 : Int)/10^30,(-431477297825712466910701439 : Int)/10^30)
theorem v2162_pb_checked : Scalar.distance (sourceCoefficient 25 63 1 1) v2162_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2162_pg : Scalar.QComplex := ((-93086383602897914159830 : Int)/10^30,(90959574254754439923 : Int)/10^30)
theorem v2162_pg_checked : Scalar.distance (sourceCoefficient 25 63 1 2) v2162_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2162_mb : Scalar.QComplex := ((-793964353927475300034146 : Int)/10^30,(-431476773328756027568569192 : Int)/10^30)
theorem v2162_mb_checked : Scalar.distance (sourceCoefficient 25 63 3 1) v2162_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2162_mg : Scalar.QComplex := ((-93086270448567126201600 : Int)/10^30,(171288896980562560681 : Int)/10^30)
theorem v2162_mg_checked : Scalar.distance (sourceCoefficient 25 63 3 2) v2162_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2162_upper : Scalar.QComplex := ((999996346729782246837490303388 : Int)/10^30,(-2703058839374948030499238773 : Int)/10^30)
theorem v2162_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 63 5) 1) 14) v2162_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2162 : Material (25 : Basis) (63 : Basis) where
  plus := ![v2162_pa,v2162_pb,v2162_pg]
  minus := ![(Primitive.Addresses.material2162 1).one,v2162_mb,v2162_mg]
  upper := v2162_upper
  lower := (Primitive.Addresses.material2162 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2162_pa_checked.trans (by decide +kernel)
    · exact v2162_pb_checked.trans (by decide +kernel)
    · exact v2162_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 63 Primitive.Addresses.material2162
    · exact v2162_mb_checked.trans (by decide +kernel)
    · exact v2162_mg_checked.trans (by decide +kernel)
  upper_error := v2162_upper_checked
  lower_error := reuse_lower_error 25 63 Primitive.Addresses.material2162

def v2163_pa : Scalar.QComplex := ((999999487331534060432648615857 : Int)/10^30,(-1012589091907560859805515230 : Int)/10^30)
theorem v2163_pa_checked : Scalar.distance (sourceCoefficient 25 64 1 0) v2163_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2163_pb : Scalar.QComplex := ((-436909411156154155877143 : Int)/10^30,(-431477280032127753427866157 : Int)/10^30)
theorem v2163_pb_checked : Scalar.distance (sourceCoefficient 25 64 1 1) v2163_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2163_pg : Scalar.QComplex := ((-93086380042610800053044 : Int)/10^30,(94258301359568126479 : Int)/10^30)
theorem v2163_pg_checked : Scalar.distance (sourceCoefficient 25 64 1 2) v2163_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2163_mb : Scalar.QComplex := ((-809254708127233677340210 : Int)/10^30,(-431476742340272753254881252 : Int)/10^30)
theorem v2163_mb_checked : Scalar.distance (sourceCoefficient 25 64 3 1) v2163_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2163_mg : Scalar.QComplex := ((-93086264041628415451863 : Int)/10^30,(174587619784741956744 : Int)/10^30)
theorem v2163_mg_checked : Scalar.distance (sourceCoefficient 25 64 3 2) v2163_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2163_upper : Scalar.QComplex := ((999996250312854603971226593187 : Int)/10^30,(-2738495979664452455848046714 : Int)/10^30)
theorem v2163_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 64 5) 1) 14) v2163_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2163 : Material (25 : Basis) (64 : Basis) where
  plus := ![v2163_pa,v2163_pb,v2163_pg]
  minus := ![(Primitive.Addresses.material2163 1).one,v2163_mb,v2163_mg]
  upper := v2163_upper
  lower := (Primitive.Addresses.material2163 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2163_pa_checked.trans (by decide +kernel)
    · exact v2163_pb_checked.trans (by decide +kernel)
    · exact v2163_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 64 Primitive.Addresses.material2163
    · exact v2163_mb_checked.trans (by decide +kernel)
    · exact v2163_mg_checked.trans (by decide +kernel)
  upper_error := v2163_upper_checked
  lower_error := reuse_lower_error 25 64 Primitive.Addresses.material2163

def v2164_pa : Scalar.QComplex := ((999999450265329617618337197837 : Int)/10^30,(-1048555691680969087275113665 : Int)/10^30)
theorem v2164_pa_checked : Scalar.distance (sourceCoefficient 25 65 1 0) v2164_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2164_pb : Scalar.QComplex := ((-452428186813303829201855 : Int)/10^30,(-431477261234015850598427475 : Int)/10^30)
theorem v2164_pb_checked : Scalar.distance (sourceCoefficient 25 65 1 1) v2164_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2164_pg : Scalar.QComplex := ((-93086376289689703985551 : Int)/10^30,(97606303334079539041 : Int)/10^30)
theorem v2164_pg_checked : Scalar.distance (sourceCoefficient 25 65 1 2) v2164_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2164_mb : Scalar.QComplex := ((-824773461784109993812957 : Int)/10^30,(-431476710150163397411188470 : Int)/10^30)
theorem v2164_mb_checked : Scalar.distance (sourceCoefficient 25 65 3 1) v2164_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2164_mg : Scalar.QComplex := ((-93086257399533801176464 : Int)/10^30,(177935617274037342331 : Int)/10^30)
theorem v2164_mg_checked : Scalar.distance (sourceCoefficient 25 65 3 2) v2164_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2164_upper : Scalar.QComplex := ((999996151171617022455075210516 : Int)/10^30,(-2774462461896929005923079021 : Int)/10^30)
theorem v2164_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 65 5) 1) 14) v2164_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2164 : Material (25 : Basis) (65 : Basis) where
  plus := ![v2164_pa,v2164_pb,v2164_pg]
  minus := ![(Primitive.Addresses.material2164 1).one,v2164_mb,v2164_mg]
  upper := v2164_upper
  lower := (Primitive.Addresses.material2164 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2164_pa_checked.trans (by decide +kernel)
    · exact v2164_pb_checked.trans (by decide +kernel)
    · exact v2164_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 65 Primitive.Addresses.material2164
    · exact v2164_mb_checked.trans (by decide +kernel)
    · exact v2164_mg_checked.trans (by decide +kernel)
  upper_error := v2164_upper_checked
  lower_error := reuse_lower_error 25 65 Primitive.Addresses.material2164

def v2165_pa : Scalar.QComplex := ((999999431669125478281739845302 : Int)/10^30,(-1066143248369305008041444276 : Int)/10^30)
theorem v2165_pa_checked : Scalar.distance (sourceCoefficient 25 66 1 0) v2165_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2165_pb : Scalar.QComplex := ((-460016820242208284638920 : Int)/10^30,(-431477251770861312765806646 : Int)/10^30)
theorem v2165_pb_checked : Scalar.distance (sourceCoefficient 25 66 1 1) v2165_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2165_pg : Scalar.QComplex := ((-93086374403377914553613 : Int)/10^30,(99243465988464472032 : Int)/10^30)
theorem v2165_pg_checked : Scalar.distance (sourceCoefficient 25 66 1 2) v2165_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2165_mb : Scalar.QComplex := ((-832362084221143244497423 : Int)/10^30,(-431476694138363513361136115 : Int)/10^30)
theorem v2165_mb_checked : Scalar.distance (sourceCoefficient 25 66 3 1) v2165_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2165_mg : Scalar.QComplex := ((-93086254100425078439196 : Int)/10^30,(179572777691029679114 : Int)/10^30)
theorem v2165_mg_checked : Scalar.distance (sourceCoefficient 25 66 3 2) v2165_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2165_upper : Scalar.QComplex := ((999996102220913266591444720263 : Int)/10^30,(-2792049960295303908914978109 : Int)/10^30)
theorem v2165_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 66 5) 1) 14) v2165_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2165 : Material (25 : Basis) (66 : Basis) where
  plus := ![v2165_pa,v2165_pb,v2165_pg]
  minus := ![(Primitive.Addresses.material2165 1).one,v2165_mb,v2165_mg]
  upper := v2165_upper
  lower := (Primitive.Addresses.material2165 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2165_pa_checked.trans (by decide +kernel)
    · exact v2165_pb_checked.trans (by decide +kernel)
    · exact v2165_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 66 Primitive.Addresses.material2165
    · exact v2165_mb_checked.trans (by decide +kernel)
    · exact v2165_mg_checked.trans (by decide +kernel)
  upper_error := v2165_upper_checked
  lower_error := reuse_lower_error 25 66 Primitive.Addresses.material2165

def v2166_pa : Scalar.QComplex := ((999999399763978999054216891568 : Int)/10^30,(-1095660386122730394650762719 : Int)/10^30)
theorem v2166_pa_checked : Scalar.distance (sourceCoefficient 25 67 1 0) v2166_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2166_pb : Scalar.QComplex := ((-472752798202228307990627 : Int)/10^30,(-431477235488930441834607118 : Int)/10^30)
theorem v2166_pb_checked : Scalar.distance (sourceCoefficient 25 67 1 1) v2166_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2166_pg : Scalar.QComplex := ((-93086371162087949287773 : Int)/10^30,(101991110588955475534 : Int)/10^30)
theorem v2166_pg_checked : Scalar.distance (sourceCoefficient 25 67 1 2) v2166_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2166_mb : Scalar.QComplex := ((-845098043388403579717429 : Int)/10^30,(-431476666865863332593661528 : Int)/10^30)
theorem v2166_mb_checked : Scalar.distance (sourceCoefficient 25 67 3 1) v2166_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2166_mg : Scalar.QComplex := ((-93086248488042779149024 : Int)/10^30,(182320418471359766548 : Int)/10^30)
theorem v2166_mg_checked : Scalar.distance (sourceCoefficient 25 67 3 2) v2166_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2166_upper : Scalar.QComplex := ((999996019371912317738913110819 : Int)/10^30,(-2821566999021031527496090373 : Int)/10^30)
theorem v2166_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 67 5) 1) 14) v2166_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2166 : Material (25 : Basis) (67 : Basis) where
  plus := ![v2166_pa,v2166_pb,v2166_pg]
  minus := ![(Primitive.Addresses.material2166 1).one,v2166_mb,v2166_mg]
  upper := v2166_upper
  lower := (Primitive.Addresses.material2166 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2166_pa_checked.trans (by decide +kernel)
    · exact v2166_pb_checked.trans (by decide +kernel)
    · exact v2166_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 67 Primitive.Addresses.material2166
    · exact v2166_mb_checked.trans (by decide +kernel)
    · exact v2166_mg_checked.trans (by decide +kernel)
  upper_error := v2166_upper_checked
  lower_error := reuse_lower_error 25 67 Primitive.Addresses.material2166

def v2167_pa : Scalar.QComplex := ((999999344695271389364620266162 : Int)/10^30,(-1144818338338875239040044326 : Int)/10^30)
theorem v2167_pa_checked : Scalar.distance (sourceCoefficient 25 68 1 0) v2167_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2167_pb : Scalar.QComplex := ((-493963343143516131773901 : Int)/10^30,(-431477207260445427769859371 : Int)/10^30)
theorem v2167_pb_checked : Scalar.distance (sourceCoefficient 25 68 1 1) v2167_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2167_pg : Scalar.QComplex := ((-93086365554023926545002 : Int)/10^30,(106567048169453364698 : Int)/10^30)
theorem v2167_pg_checked : Scalar.distance (sourceCoefficient 25 68 1 2) v2167_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2167_mb : Scalar.QComplex := ((-866308556072124948699505 : Int)/10^30,(-431476620333643832434815450 : Int)/10^30)
theorem v2167_mb_checked : Scalar.distance (sourceCoefficient 25 68 3 1) v2167_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2167_mg : Scalar.QComplex := ((-93086238931152805153222 : Int)/10^30,(186896349508520290015 : Int)/10^30)
theorem v2167_mg_checked : Scalar.distance (sourceCoefficient 25 68 3 2) v2167_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2167_upper : Scalar.QComplex := ((999995879461120775943238628308 : Int)/10^30,(-2870724782978587504446449715 : Int)/10^30)
theorem v2167_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 68 5) 1) 14) v2167_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2167 : Material (25 : Basis) (68 : Basis) where
  plus := ![v2167_pa,v2167_pb,v2167_pg]
  minus := ![(Primitive.Addresses.material2167 1).one,v2167_mb,v2167_mg]
  upper := v2167_upper
  lower := (Primitive.Addresses.material2167 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2167_pa_checked.trans (by decide +kernel)
    · exact v2167_pb_checked.trans (by decide +kernel)
    · exact v2167_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 68 Primitive.Addresses.material2167
    · exact v2167_mb_checked.trans (by decide +kernel)
    · exact v2167_mg_checked.trans (by decide +kernel)
  upper_error := v2167_upper_checked
  lower_error := reuse_lower_error 25 68 Primitive.Addresses.material2167

def v2168_pa : Scalar.QComplex := ((999999319692637868459088050092 : Int)/10^30,(-1166453711659821867585839494 : Int)/10^30)
theorem v2168_pa_checked : Scalar.distance (sourceCoefficient 25 69 1 0) v2168_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2168_pb : Scalar.QComplex := ((-503298517297419899459400 : Int)/10^30,(-431477194395959312875736385 : Int)/10^30)
theorem v2168_pb_checked : Scalar.distance (sourceCoefficient 25 69 1 1) v2168_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2168_pg : Scalar.QComplex := ((-93086363002636770025154 : Int)/10^30,(108581007497797969476 : Int)/10^30)
theorem v2168_pg_checked : Scalar.distance (sourceCoefficient 25 69 1 2) v2168_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2168_mb : Scalar.QComplex := ((-875643715648644618144262 : Int)/10^30,(-431476599413327653394259353 : Int)/10^30)
theorem v2168_mb_checked : Scalar.distance (sourceCoefficient 25 69 3 1) v2168_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2168_mg : Scalar.QComplex := ((-93086234641810403631030 : Int)/10^30,(188910305885243588497 : Int)/10^30)
theorem v2168_mg_checked : Scalar.distance (sourceCoefficient 25 69 3 2) v2168_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2168_upper : Scalar.QComplex := ((999995817117832887304987278098 : Int)/10^30,(-2892360080923909805032710057 : Int)/10^30)
theorem v2168_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 69 5) 1) 14) v2168_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2168 : Material (25 : Basis) (69 : Basis) where
  plus := ![v2168_pa,v2168_pb,v2168_pg]
  minus := ![(Primitive.Addresses.material2168 1).one,v2168_mb,v2168_mg]
  upper := v2168_upper
  lower := (Primitive.Addresses.material2168 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2168_pa_checked.trans (by decide +kernel)
    · exact v2168_pb_checked.trans (by decide +kernel)
    · exact v2168_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 69 Primitive.Addresses.material2168
    · exact v2168_mb_checked.trans (by decide +kernel)
    · exact v2168_mg_checked.trans (by decide +kernel)
  upper_error := v2168_upper_checked
  lower_error := reuse_lower_error 25 69 Primitive.Addresses.material2168

def v2169_pa : Scalar.QComplex := ((999999302990433750668730458282 : Int)/10^30,(-1180685668023596827467360436 : Int)/10^30)
theorem v2169_pa_checked : Scalar.distance (sourceCoefficient 25 70 1 0) v2169_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2169_pb : Scalar.QComplex := ((-509439284421614861649553 : Int)/10^30,(-431477185786741254710446446 : Int)/10^30)
theorem v2169_pb_checked : Scalar.distance (sourceCoefficient 25 70 1 1) v2169_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2169_pg : Scalar.QComplex := ((-93086361296591433101359 : Int)/10^30,(109905809276752397392 : Int)/10^30)
theorem v2169_pg_checked : Scalar.distance (sourceCoefficient 25 70 1 2) v2169_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2169_mb : Scalar.QComplex := ((-881784473056983893665747 : Int)/10^30,(-431476585504907342538577836 : Int)/10^30)
theorem v2169_mb_checked : Scalar.distance (sourceCoefficient 25 70 3 1) v2169_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2169_mg : Scalar.QComplex := ((-93086231792521433565398 : Int)/10^30,(190235105698673479341 : Int)/10^30)
theorem v2169_mg_checked : Scalar.distance (sourceCoefficient 25 70 3 2) v2169_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2169_upper : Scalar.QComplex := ((999995775852588074605804086975 : Int)/10^30,(-2906591987264368468918896245 : Int)/10^30)
theorem v2169_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 70 5) 1) 14) v2169_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2169 : Material (25 : Basis) (70 : Basis) where
  plus := ![v2169_pa,v2169_pb,v2169_pg]
  minus := ![(Primitive.Addresses.material2169 1).one,v2169_mb,v2169_mg]
  upper := v2169_upper
  lower := (Primitive.Addresses.material2169 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2169_pa_checked.trans (by decide +kernel)
    · exact v2169_pb_checked.trans (by decide +kernel)
    · exact v2169_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 70 Primitive.Addresses.material2169
    · exact v2169_mb_checked.trans (by decide +kernel)
    · exact v2169_mg_checked.trans (by decide +kernel)
  upper_error := v2169_upper_checked
  lower_error := reuse_lower_error 25 70 Primitive.Addresses.material2169

def v2170_pa : Scalar.QComplex := ((999999274013183206047259693833 : Int)/10^30,(-1204978467247878800034436723 : Int)/10^30)
theorem v2170_pa_checked : Scalar.distance (sourceCoefficient 25 71 1 0) v2170_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2170_pb : Scalar.QComplex := ((-519921077405749015096259 : Int)/10^30,(-431477170822295699885351844 : Int)/10^30)
theorem v2170_pb_checked : Scalar.distance (sourceCoefficient 25 71 1 1) v2170_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2170_pg : Scalar.QComplex := ((-93086358333691487548083 : Int)/10^30,(112167138818482437635 : Int)/10^30)
theorem v2170_pg_checked : Scalar.distance (sourceCoefficient 25 71 1 2) v2170_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2170_mb : Scalar.QComplex := ((-892266249224624937309454 : Int)/10^30,(-431476561495152096784179617 : Int)/10^30)
theorem v2170_mb_checked : Scalar.distance (sourceCoefficient 25 71 3 1) v2170_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2170_mg : Scalar.QComplex := ((-93086226878197043223997 : Int)/10^30,(192496431841557974380 : Int)/10^30)
theorem v2170_mg_checked : Scalar.distance (sourceCoefficient 25 71 3 2) v2170_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2170_upper : Scalar.QComplex := ((999995704948213052614714493170 : Int)/10^30,(-2930884700295273985189344217 : Int)/10^30)
theorem v2170_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 71 5) 1) 14) v2170_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2170 : Material (25 : Basis) (71 : Basis) where
  plus := ![v2170_pa,v2170_pb,v2170_pg]
  minus := ![(Primitive.Addresses.material2170 1).one,v2170_mb,v2170_mg]
  upper := v2170_upper
  lower := (Primitive.Addresses.material2170 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2170_pa_checked.trans (by decide +kernel)
    · exact v2170_pb_checked.trans (by decide +kernel)
    · exact v2170_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 71 Primitive.Addresses.material2170
    · exact v2170_mb_checked.trans (by decide +kernel)
    · exact v2170_mg_checked.trans (by decide +kernel)
  upper_error := v2170_upper_checked
  lower_error := reuse_lower_error 25 71 Primitive.Addresses.material2170

def v2171_pa : Scalar.QComplex := ((999999241899292554877324071547 : Int)/10^30,(-1231341073859539017960874044 : Int)/10^30)
theorem v2171_pa_checked : Scalar.distance (sourceCoefficient 25 72 1 0) v2171_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2171_pb : Scalar.QComplex := ((-531295945172727880058819 : Int)/10^30,(-431477154198708786591570540 : Int)/10^30)
theorem v2171_pb_checked : Scalar.distance (sourceCoefficient 25 72 1 1) v2171_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2171_pg : Scalar.QComplex := ((-93086355045831668283901 : Int)/10^30,(114621139278171459751 : Int)/10^30)
theorem v2171_pg_checked : Scalar.distance (sourceCoefficient 25 72 1 2) v2171_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2171_mb : Scalar.QComplex := ((-903641098410813867876412 : Int)/10^30,(-431476535055572795335349332 : Int)/10^30)
theorem v2171_mb_checked : Scalar.distance (sourceCoefficient 25 72 3 1) v2171_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2171_mg : Scalar.QComplex := ((-93086221472646575546521 : Int)/10^30,(194950428550235527676 : Int)/10^30)
theorem v2171_mg_checked : Scalar.distance (sourceCoefficient 25 72 3 2) v2171_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2171_upper : Scalar.QComplex := ((999995627334902816576684434426 : Int)/10^30,(-2957247212217266509839400378 : Int)/10^30)
theorem v2171_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 72 5) 1) 14) v2171_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2171 : Material (25 : Basis) (72 : Basis) where
  plus := ![v2171_pa,v2171_pb,v2171_pg]
  minus := ![(Primitive.Addresses.material2171 1).one,v2171_mb,v2171_mg]
  upper := v2171_upper
  lower := (Primitive.Addresses.material2171 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2171_pa_checked.trans (by decide +kernel)
    · exact v2171_pb_checked.trans (by decide +kernel)
    · exact v2171_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 72 Primitive.Addresses.material2171
    · exact v2171_mb_checked.trans (by decide +kernel)
    · exact v2171_mg_checked.trans (by decide +kernel)
  upper_error := v2171_upper_checked
  lower_error := reuse_lower_error 25 72 Primitive.Addresses.material2171

def v2172_pa : Scalar.QComplex := ((999999230218911612085310988789 : Int)/10^30,(-1240790709270868669627717913 : Int)/10^30)
theorem v2172_pa_checked : Scalar.distance (sourceCoefficient 25 73 1 0) v2172_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2172_pb : Scalar.QComplex := ((-535373248798310827650702 : Int)/10^30,(-431477148142664753642177356 : Int)/10^30)
theorem v2172_pb_checked : Scalar.distance (sourceCoefficient 25 73 1 1) v2172_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2172_pg : Scalar.QComplex := ((-93086353848927439353918 : Int)/10^30,(115500771925959656003 : Int)/10^30)
theorem v2172_pg_checked : Scalar.distance (sourceCoefficient 25 73 1 2) v2172_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2172_mb : Scalar.QComplex := ((-907718395292137087345403 : Int)/10^30,(-431476525481001623388287641 : Int)/10^30)
theorem v2172_mb_checked : Scalar.distance (sourceCoefficient 25 73 3 1) v2172_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2172_mg : Scalar.QComplex := ((-93086219516659434421267 : Int)/10^30,(195830059837621844957 : Int)/10^30)
theorem v2172_mg_checked : Scalar.distance (sourceCoefficient 25 73 3 2) v2172_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2172_upper : Scalar.QComplex := ((999995599345325814612968109863 : Int)/10^30,(-2966696813395196377104342827 : Int)/10^30)
theorem v2172_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 73 5) 1) 14) v2172_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2172 : Material (25 : Basis) (73 : Basis) where
  plus := ![v2172_pa,v2172_pb,v2172_pg]
  minus := ![(Primitive.Addresses.material2172 1).one,v2172_mb,v2172_mg]
  upper := v2172_upper
  lower := (Primitive.Addresses.material2172 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2172_pa_checked.trans (by decide +kernel)
    · exact v2172_pb_checked.trans (by decide +kernel)
    · exact v2172_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 73 Primitive.Addresses.material2172
    · exact v2172_mb_checked.trans (by decide +kernel)
    · exact v2172_mg_checked.trans (by decide +kernel)
  upper_error := v2172_upper_checked
  lower_error := reuse_lower_error 25 73 Primitive.Addresses.material2172

def v2173_pa : Scalar.QComplex := ((999999216968840031737141425089 : Int)/10^30,(-1251423871755181213231094194 : Int)/10^30)
theorem v2173_pa_checked : Scalar.distance (sourceCoefficient 25 74 1 0) v2173_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2173_pb : Scalar.QComplex := ((-539961217504289969703386 : Int)/10^30,(-431477141266700400363755761 : Int)/10^30)
theorem v2173_pb_checked : Scalar.distance (sourceCoefficient 25 74 1 1) v2173_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2173_pg : Scalar.QComplex := ((-93086352490520460546103 : Int)/10^30,(116490574857004625800 : Int)/10^30)
theorem v2173_pg_checked : Scalar.distance (sourceCoefficient 25 74 1 2) v2173_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2173_mb : Scalar.QComplex := ((-912306356356158244693022 : Int)/10^30,(-431476514645829471525528605 : Int)/10^30)
theorem v2173_mb_checked : Scalar.distance (sourceCoefficient 25 74 3 1) v2173_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2173_mg : Scalar.QComplex := ((-93086217304097610987806 : Int)/10^30,(196819861227873904966 : Int)/10^30)
theorem v2173_mg_checked : Scalar.distance (sourceCoefficient 25 74 3 2) v2173_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2173_upper : Scalar.QComplex := ((999995567743400153731782106267 : Int)/10^30,(-2977329937174240948754232407 : Int)/10^30)
theorem v2173_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 74 5) 1) 14) v2173_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2173 : Material (25 : Basis) (74 : Basis) where
  plus := ![v2173_pa,v2173_pb,v2173_pg]
  minus := ![(Primitive.Addresses.material2173 1).one,v2173_mb,v2173_mg]
  upper := v2173_upper
  lower := (Primitive.Addresses.material2173 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2173_pa_checked.trans (by decide +kernel)
    · exact v2173_pb_checked.trans (by decide +kernel)
    · exact v2173_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 74 Primitive.Addresses.material2173
    · exact v2173_mb_checked.trans (by decide +kernel)
    · exact v2173_mg_checked.trans (by decide +kernel)
  upper_error := v2173_upper_checked
  lower_error := reuse_lower_error 25 74 Primitive.Addresses.material2173

def v2174_pa : Scalar.QComplex := ((999999198319090075328870630847 : Int)/10^30,(-1266238988957874776863258839 : Int)/10^30)
theorem v2174_pa_checked : Scalar.distance (sourceCoefficient 25 75 1 0) v2174_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2174_pb : Scalar.QComplex := ((-546353604849042036103646 : Int)/10^30,(-431477131578012901121889677 : Int)/10^30)
theorem v2174_pb_checked : Scalar.distance (sourceCoefficient 25 75 1 1) v2174_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2174_pg : Scalar.QComplex := ((-93086350577388373109641 : Int)/10^30,(117869660934747567219 : Int)/10^30)
theorem v2174_pg_checked : Scalar.distance (sourceCoefficient 25 75 1 2) v2174_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2174_mb : Scalar.QComplex := ((-918698732959831406548806 : Int)/10^30,(-431476499440803203742346825 : Int)/10^30)
theorem v2174_mb_checked : Scalar.distance (sourceCoefficient 25 75 3 1) v2174_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2174_mg : Scalar.QComplex := ((-93086214200877062536942 : Int)/10^30,(198198945141173245106 : Int)/10^30)
theorem v2174_mg_checked : Scalar.distance (sourceCoefficient 25 75 3 2) v2174_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2174_upper : Scalar.QComplex := ((999995523524129699019971266660 : Int)/10^30,(-2992145000123781212229819528 : Int)/10^30)
theorem v2174_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 75 5) 1) 14) v2174_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2174 : Material (25 : Basis) (75 : Basis) where
  plus := ![v2174_pa,v2174_pb,v2174_pg]
  minus := ![(Primitive.Addresses.material2174 1).one,v2174_mb,v2174_mg]
  upper := v2174_upper
  lower := (Primitive.Addresses.material2174 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2174_pa_checked.trans (by decide +kernel)
    · exact v2174_pb_checked.trans (by decide +kernel)
    · exact v2174_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 75 Primitive.Addresses.material2174
    · exact v2174_mb_checked.trans (by decide +kernel)
    · exact v2174_mg_checked.trans (by decide +kernel)
  upper_error := v2174_upper_checked
  lower_error := reuse_lower_error 25 75 Primitive.Addresses.material2174

def v2175_pa : Scalar.QComplex := ((999999182502250541726693364116 : Int)/10^30,(-1278669163862950221231420350 : Int)/10^30)
theorem v2175_pa_checked : Scalar.distance (sourceCoefficient 25 76 1 0) v2175_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2175_pb : Scalar.QComplex := ((-551716943569336065603715 : Int)/10^30,(-431477123351596053639835275 : Int)/10^30)
theorem v2175_pb_checked : Scalar.distance (sourceCoefficient 25 76 1 1) v2175_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2175_pg : Scalar.QComplex := ((-93086348953843280881056 : Int)/10^30,(119026741287958727279 : Int)/10^30)
theorem v2175_pg_checked : Scalar.distance (sourceCoefficient 25 76 1 2) v2175_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2175_mb : Scalar.QComplex := ((-924062062584082078478921 : Int)/10^30,(-431476486586069659526492023 : Int)/10^30)
theorem v2175_mb_checked : Scalar.distance (sourceCoefficient 25 76 3 1) v2175_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2175_mg : Scalar.QComplex := ((-93086211578824342971748 : Int)/10^30,(199356023662504215645 : Int)/10^30)
theorem v2175_mg_checked : Scalar.distance (sourceCoefficient 25 76 3 2) v2175_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2175_upper : Scalar.QComplex := ((999995486253959493240703871916 : Int)/10^30,(-3004575129217141143878829769 : Int)/10^30)
theorem v2175_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 76 5) 1) 14) v2175_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2175 : Material (25 : Basis) (76 : Basis) where
  plus := ![v2175_pa,v2175_pb,v2175_pg]
  minus := ![(Primitive.Addresses.material2175 1).one,v2175_mb,v2175_mg]
  upper := v2175_upper
  lower := (Primitive.Addresses.material2175 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2175_pa_checked.trans (by decide +kernel)
    · exact v2175_pb_checked.trans (by decide +kernel)
    · exact v2175_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 76 Primitive.Addresses.material2175
    · exact v2175_mb_checked.trans (by decide +kernel)
    · exact v2175_mg_checked.trans (by decide +kernel)
  upper_error := v2175_upper_checked
  lower_error := reuse_lower_error 25 76 Primitive.Addresses.material2175

def v2176_pa : Scalar.QComplex := ((999999178818492130856293774026 : Int)/10^30,(-1281546854937117992149989335 : Int)/10^30)
theorem v2176_pa_checked : Scalar.distance (sourceCoefficient 25 77 1 0) v2176_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2176_pb : Scalar.QComplex := ((-552958602031005132096736 : Int)/10^30,(-431477121434439222902492052 : Int)/10^30)
theorem v2176_pb_checked : Scalar.distance (sourceCoefficient 25 77 1 1) v2176_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2176_pg : Scalar.QComplex := ((-93086348575586792136755 : Int)/10^30,(119294615217155531434 : Int)/10^30)
theorem v2176_pg_checked : Scalar.distance (sourceCoefficient 25 77 1 2) v2176_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2176_mb : Scalar.QComplex := ((-925303718929004953709544 : Int)/10^30,(-431476483597418212435034039 : Int)/10^30)
theorem v2176_mb_checked : Scalar.distance (sourceCoefficient 25 77 3 1) v2176_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2176_mg : Scalar.QComplex := ((-93086210969404858766694 : Int)/10^30,(199623897165540999769 : Int)/10^30)
theorem v2176_mg_checked : Scalar.distance (sourceCoefficient 25 77 3 2) v2176_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2176_upper : Scalar.QComplex := ((999995477603572836977103335913 : Int)/10^30,(-3007452809647493267954095124 : Int)/10^30)
theorem v2176_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 25 77 5) 1) 14) v2176_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2176 : Material (25 : Basis) (77 : Basis) where
  plus := ![v2176_pa,v2176_pb,v2176_pg]
  minus := ![(Primitive.Addresses.material2176 1).one,v2176_mb,v2176_mg]
  upper := v2176_upper
  lower := (Primitive.Addresses.material2176 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2176_pa_checked.trans (by decide +kernel)
    · exact v2176_pb_checked.trans (by decide +kernel)
    · exact v2176_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 25 77 Primitive.Addresses.material2176
    · exact v2176_mb_checked.trans (by decide +kernel)
    · exact v2176_mg_checked.trans (by decide +kernel)
  upper_error := v2176_upper_checked
  lower_error := reuse_lower_error 25 77 Primitive.Addresses.material2176

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
