import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B036
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B037

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v881_pa : Scalar.QComplex := ((999999862898112918971863624247 : Int)/10^30,(-523644684270860169277638987 : Int)/10^30)
theorem v881_pa_checked : Scalar.distance (sourceCoefficient 9 54 1 0) v881_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v881_pb : Scalar.QComplex := ((-225940891056681907173214 : Int)/10^30,(-431477425182625029969149702 : Int)/10^30)
theorem v881_pb_checked : Scalar.distance (sourceCoefficient 9 54 1 1) v881_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v881_pg : Scalar.QComplex := ((-93086413179981713429376 : Int)/10^30,(48744212122461827353 : Int)/10^30)
theorem v881_pg_checked : Scalar.distance (sourceCoefficient 9 54 1 2) v881_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v881_mb : Scalar.QComplex := ((-598286391839325013284952 : Int)/10^30,(-431477069547047160050142506 : Int)/10^30)
theorem v881_mb_checked : Scalar.distance (sourceCoefficient 9 54 3 1) v881_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v881_mg : Scalar.QComplex := ((-93086336455596123409114 : Int)/10^30,(129073576090669823690 : Int)/10^30)
theorem v881_mg_checked : Scalar.distance (sourceCoefficient 9 54 3 2) v881_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v881_upper : Scalar.QComplex := ((999997469752564990988420044294 : Int)/10^30,(-2249552948446855471398633764 : Int)/10^30)
theorem v881_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 54 5) 1) 14) v881_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material881 : Material (9 : Basis) (54 : Basis) where
  plus := ![v881_pa,v881_pb,v881_pg]
  minus := ![(Primitive.Addresses.material881 1).one,v881_mb,v881_mg]
  upper := v881_upper
  lower := (Primitive.Addresses.material881 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v881_pa_checked.trans (by decide +kernel)
    · exact v881_pb_checked.trans (by decide +kernel)
    · exact v881_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 54 Primitive.Addresses.material881
    · exact v881_mb_checked.trans (by decide +kernel)
    · exact v881_mg_checked.trans (by decide +kernel)
  upper_error := v881_upper_checked
  lower_error := reuse_lower_error 9 54 Primitive.Addresses.material881

def v882_pa : Scalar.QComplex := ((999999854745807467033741123978 : Int)/10^30,(-538988278135204039938075655 : Int)/10^30)
theorem v882_pa_checked : Scalar.distance (sourceCoefficient 9 55 1 0) v882_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v882_pb : Scalar.QComplex := ((-232561305479592914105419 : Int)/10^30,(-431477420072483991792473308 : Int)/10^30)
theorem v882_pb_checked : Scalar.distance (sourceCoefficient 9 55 1 1) v882_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v882_pg : Scalar.QComplex := ((-93086412249319434635509 : Int)/10^30,(50172492343809310512 : Int)/10^30)
theorem v882_pg_checked : Scalar.distance (sourceCoefficient 9 55 1 2) v882_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v882_mb : Scalar.QComplex := ((-604906799387331598943342 : Int)/10^30,(-431477058723788550037248875 : Int)/10^30)
theorem v882_mb_checked : Scalar.distance (sourceCoefficient 9 55 3 1) v882_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v882_mg : Scalar.QComplex := ((-93086334292392687473695 : Int)/10^30,(130501854977083673684 : Int)/10^30)
theorem v882_mg_checked : Scalar.distance (sourceCoefficient 9 55 3 2) v882_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v882_upper : Scalar.QComplex := ((999997435118620631056089144591 : Int)/10^30,(-2264896505388579027593017751 : Int)/10^30)
theorem v882_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 55 5) 1) 14) v882_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material882 : Material (9 : Basis) (55 : Basis) where
  plus := ![v882_pa,v882_pb,v882_pg]
  minus := ![(Primitive.Addresses.material882 1).one,v882_mb,v882_mg]
  upper := v882_upper
  lower := (Primitive.Addresses.material882 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v882_pa_checked.trans (by decide +kernel)
    · exact v882_pb_checked.trans (by decide +kernel)
    · exact v882_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 55 Primitive.Addresses.material882
    · exact v882_mb_checked.trans (by decide +kernel)
    · exact v882_mg_checked.trans (by decide +kernel)
  upper_error := v882_upper_checked
  lower_error := reuse_lower_error 9 55 Primitive.Addresses.material882

def v883_pa : Scalar.QComplex := ((999999852776470967640456495287 : Int)/10^30,(-542629741527269758504997891 : Int)/10^30)
theorem v883_pa_checked : Scalar.distance (sourceCoefficient 9 56 1 0) v883_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v883_pb : Scalar.QComplex := ((-234132514729719280592552 : Int)/10^30,(-431477418839818450773684531 : Int)/10^30)
theorem v883_pb_checked : Scalar.distance (sourceCoefficient 9 56 1 1) v883_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v883_pg : Scalar.QComplex := ((-93086412024693308132605 : Int)/10^30,(50511463133136124433 : Int)/10^30)
theorem v883_pg_checked : Scalar.distance (sourceCoefficient 9 56 1 2) v883_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v883_mb : Scalar.QComplex := ((-606478006988690109094176 : Int)/10^30,(-431477056135240649774841200 : Int)/10^30)
theorem v883_mb_checked : Scalar.distance (sourceCoefficient 9 56 3 1) v883_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v883_mg : Scalar.QComplex := ((-93086333775250120097949 : Int)/10^30,(130840825446353940621 : Int)/10^30)
theorem v883_mg_checked : Scalar.distance (sourceCoefficient 9 56 3 2) v883_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v883_upper : Scalar.QComplex := ((999997426864451601031123576079 : Int)/10^30,(-2268537959958216638875153375 : Int)/10^30)
theorem v883_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 56 5) 1) 14) v883_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material883 : Material (9 : Basis) (56 : Basis) where
  plus := ![v883_pa,v883_pb,v883_pg]
  minus := ![(Primitive.Addresses.material883 1).one,v883_mb,v883_mg]
  upper := v883_upper
  lower := (Primitive.Addresses.material883 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v883_pa_checked.trans (by decide +kernel)
    · exact v883_pb_checked.trans (by decide +kernel)
    · exact v883_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 56 Primitive.Addresses.material883
    · exact v883_mb_checked.trans (by decide +kernel)
    · exact v883_mg_checked.trans (by decide +kernel)
  upper_error := v883_upper_checked
  lower_error := reuse_lower_error 9 56 Primitive.Addresses.material883

def v884_pa : Scalar.QComplex := ((999999846316096878645101643219 : Int)/10^30,(-554407596109548013919675744 : Int)/10^30)
theorem v884_pa_checked : Scalar.distance (sourceCoefficient 9 57 1 0) v884_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v884_pb : Scalar.QComplex := ((-239214393078607610605050 : Int)/10^30,(-431477414800677632916122709 : Int)/10^30)
theorem v884_pb_checked : Scalar.distance (sourceCoefficient 9 57 1 1) v884_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v884_pg : Scalar.QComplex := ((-93086411288307090016198 : Int)/10^30,(51607821444106459285 : Int)/10^30)
theorem v884_pg_checked : Scalar.distance (sourceCoefficient 9 57 1 2) v884_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v884_mb : Scalar.QComplex := ((-611559879959766266839775 : Int)/10^30,(-431477047710669200087809693 : Int)/10^30)
theorem v884_mb_checked : Scalar.distance (sourceCoefficient 9 57 3 1) v884_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v884_mg : Scalar.QComplex := ((-93086332092756331949710 : Int)/10^30,(131937182713631829619 : Int)/10^30)
theorem v884_mg_checked : Scalar.distance (sourceCoefficient 9 57 3 2) v884_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v884_upper : Scalar.QComplex := ((999997400076578603613023924115 : Int)/10^30,(-2280315785848744420926024605 : Int)/10^30)
theorem v884_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 57 5) 1) 14) v884_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material884 : Material (9 : Basis) (57 : Basis) where
  plus := ![v884_pa,v884_pb,v884_pg]
  minus := ![(Primitive.Addresses.material884 1).one,v884_mb,v884_mg]
  upper := v884_upper
  lower := (Primitive.Addresses.material884 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v884_pa_checked.trans (by decide +kernel)
    · exact v884_pb_checked.trans (by decide +kernel)
    · exact v884_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 57 Primitive.Addresses.material884
    · exact v884_mb_checked.trans (by decide +kernel)
    · exact v884_mg_checked.trans (by decide +kernel)
  upper_error := v884_upper_checked
  lower_error := reuse_lower_error 9 57 Primitive.Addresses.material884

def v885_pa : Scalar.QComplex := ((999999842752707691109159065731 : Int)/10^30,(-560798145406233260833764316 : Int)/10^30)
theorem v885_pa_checked : Scalar.distance (sourceCoefficient 9 58 1 0) v885_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v885_pb : Scalar.QComplex := ((-241971770806527834110644 : Int)/10^30,(-431477412575681011408994942 : Int)/10^30)
theorem v885_pb_checked : Scalar.distance (sourceCoefficient 9 58 1 1) v885_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v885_pg : Scalar.QComplex := ((-93086410882446482631485 : Int)/10^30,(52202694794131004358 : Int)/10^30)
theorem v885_pg_checked : Scalar.distance (sourceCoefficient 9 58 1 2) v885_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v885_mb : Scalar.QComplex := ((-614317254740916869620275 : Int)/10^30,(-431477043106180615536260640 : Int)/10^30)
theorem v885_mb_checked : Scalar.distance (sourceCoefficient 9 58 3 1) v885_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v885_mg : Scalar.QComplex := ((-93086331173546966715382 : Int)/10^30,(132532055491918414533 : Int)/10^30)
theorem v885_mg_checked : Scalar.distance (sourceCoefficient 9 58 3 2) v885_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v885_upper : Scalar.QComplex := ((999997385483686383351422164351 : Int)/10^30,(-2286706319477370707535512038 : Int)/10^30)
theorem v885_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 58 5) 1) 14) v885_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material885 : Material (9 : Basis) (58 : Basis) where
  plus := ![v885_pa,v885_pb,v885_pg]
  minus := ![(Primitive.Addresses.material885 1).one,v885_mb,v885_mg]
  upper := v885_upper
  lower := (Primitive.Addresses.material885 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v885_pa_checked.trans (by decide +kernel)
    · exact v885_pb_checked.trans (by decide +kernel)
    · exact v885_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 58 Primitive.Addresses.material885
    · exact v885_mb_checked.trans (by decide +kernel)
    · exact v885_mg_checked.trans (by decide +kernel)
  upper_error := v885_upper_checked
  lower_error := reuse_lower_error 9 58 Primitive.Addresses.material885

def v886_pa : Scalar.QComplex := ((999999832747487523184150079624 : Int)/10^30,(-578364069579213029135997989 : Int)/10^30)
theorem v886_pa_checked : Scalar.distance (sourceCoefficient 9 59 1 0) v886_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v886_pb : Scalar.QComplex := ((-249551070399581725383153 : Int)/10^30,(-431477406338706829737677294 : Int)/10^30)
theorem v886_pb_checked : Scalar.distance (sourceCoefficient 9 59 1 1) v886_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v886_pg : Scalar.QComplex := ((-93086409743992796762852 : Int)/10^30,(53837843766568419895 : Int)/10^30)
theorem v886_pg_checked : Scalar.distance (sourceCoefficient 9 59 1 2) v886_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v886_mb : Scalar.QComplex := ((-621896546129623315402540 : Int)/10^30,(-431477030328614566351796559 : Int)/10^30)
theorem v886_mb_checked : Scalar.distance (sourceCoefficient 9 59 3 1) v886_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v886_mg : Scalar.QComplex := ((-93086328624033785907507 : Int)/10^30,(134167202873080880777 : Int)/10^30)
theorem v886_mg_checked : Scalar.distance (sourceCoefficient 9 59 3 2) v886_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v886_upper : Scalar.QComplex := ((999997345161289562656178636261 : Int)/10^30,(-2304272200219867515231148238 : Int)/10^30)
theorem v886_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 59 5) 1) 14) v886_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material886 : Material (9 : Basis) (59 : Basis) where
  plus := ![v886_pa,v886_pb,v886_pg]
  minus := ![(Primitive.Addresses.material886 1).one,v886_mb,v886_mg]
  upper := v886_upper
  lower := (Primitive.Addresses.material886 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v886_pa_checked.trans (by decide +kernel)
    · exact v886_pb_checked.trans (by decide +kernel)
    · exact v886_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 59 Primitive.Addresses.material886
    · exact v886_mb_checked.trans (by decide +kernel)
    · exact v886_mg_checked.trans (by decide +kernel)
  upper_error := v886_upper_checked
  lower_error := reuse_lower_error 9 59 Primitive.Addresses.material886

def v887_pa : Scalar.QComplex := ((999999820822244988577731930162 : Int)/10^30,(-598627996269951147702040925 : Int)/10^30)
theorem v887_pa_checked : Scalar.distance (sourceCoefficient 9 60 1 0) v887_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v887_pb : Scalar.QComplex := ((-258294497033834884043068 : Int)/10^30,(-431477398923268791908017284 : Int)/10^30)
theorem v887_pb_checked : Scalar.distance (sourceCoefficient 9 60 1 1) v887_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v887_pg : Scalar.QComplex := ((-93086408389054924835026 : Int)/10^30,(55724140118432647131 : Int)/10^30)
theorem v887_pg_checked : Scalar.distance (sourceCoefficient 9 60 1 2) v887_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v887_mb : Scalar.QComplex := ((-630639963109110096076804 : Int)/10^30,(-431477015367995893585604535 : Int)/10^30)
theorem v887_mb_checked : Scalar.distance (sourceCoefficient 9 60 3 1) v887_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v887_mg : Scalar.QComplex := ((-93086325641307622460133 : Int)/10^30,(136053497353340408874 : Int)/10^30)
theorem v887_mg_checked : Scalar.distance (sourceCoefficient 9 60 3 2) v887_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v887_upper : Scalar.QComplex := ((999997298262365650152830887241 : Int)/10^30,(-2324536076147980430804709405 : Int)/10^30)
theorem v887_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 60 5) 1) 14) v887_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material887 : Material (9 : Basis) (60 : Basis) where
  plus := ![v887_pa,v887_pb,v887_pg]
  minus := ![(Primitive.Addresses.material887 1).one,v887_mb,v887_mg]
  upper := v887_upper
  lower := (Primitive.Addresses.material887 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v887_pa_checked.trans (by decide +kernel)
    · exact v887_pb_checked.trans (by decide +kernel)
    · exact v887_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 60 Primitive.Addresses.material887
    · exact v887_mb_checked.trans (by decide +kernel)
    · exact v887_mg_checked.trans (by decide +kernel)
  upper_error := v887_upper_checked
  lower_error := reuse_lower_error 9 60 Primitive.Addresses.material887

def v888_pa : Scalar.QComplex := ((999999817297516763463406308552 : Int)/10^30,(-604487330796002544794727200 : Int)/10^30)
theorem v888_pa_checked : Scalar.distance (sourceCoefficient 9 61 1 0) v888_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v888_pb : Scalar.QComplex := ((-260822667504132147740696 : Int)/10^30,(-431477396735058126918432515 : Int)/10^30)
theorem v888_pb_checked : Scalar.distance (sourceCoefficient 9 61 1 1) v888_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v888_pg : Scalar.QComplex := ((-93086407988961801308401 : Int)/10^30,(56269564579224385653 : Int)/10^30)
theorem v888_pg_checked : Scalar.distance (sourceCoefficient 9 61 1 2) v888_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v888_mb : Scalar.QComplex := ((-633168130749726700048191 : Int)/10^30,(-431477010998088792071448563 : Int)/10^30)
theorem v888_mb_checked : Scalar.distance (sourceCoefficient 9 61 3 1) v888_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v888_mg : Scalar.QComplex := ((-93086324770537903249011 : Int)/10^30,(136598921265783347437 : Int)/10^30)
theorem v888_mg_checked : Scalar.distance (sourceCoefficient 9 61 3 2) v888_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v888_upper : Scalar.QComplex := ((999997284624962837418367653846 : Int)/10^30,(-2330395395863880181426130596 : Int)/10^30)
theorem v888_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 61 5) 1) 14) v888_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material888 : Material (9 : Basis) (61 : Basis) where
  plus := ![v888_pa,v888_pb,v888_pg]
  minus := ![(Primitive.Addresses.material888 1).one,v888_mb,v888_mg]
  upper := v888_upper
  lower := (Primitive.Addresses.material888 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v888_pa_checked.trans (by decide +kernel)
    · exact v888_pb_checked.trans (by decide +kernel)
    · exact v888_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 61 Primitive.Addresses.material888
    · exact v888_mb_checked.trans (by decide +kernel)
    · exact v888_mg_checked.trans (by decide +kernel)
  upper_error := v888_upper_checked
  lower_error := reuse_lower_error 9 61 Primitive.Addresses.material888

def v889_pa : Scalar.QComplex := ((999999812115057870487401395596 : Int)/10^30,(-613000692461496097287872784 : Int)/10^30)
theorem v889_pa_checked : Scalar.distance (sourceCoefficient 9 62 1 0) v889_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v889_pb : Scalar.QComplex := ((-264495990704352576885215 : Int)/10^30,(-431477393520484862245769662 : Int)/10^30)
theorem v889_pb_checked : Scalar.distance (sourceCoefficient 9 62 1 1) v889_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v889_pg : Scalar.QComplex := ((-93086407400999459858692 : Int)/10^30,(57062042916664235300 : Int)/10^30)
theorem v889_pg_checked : Scalar.distance (sourceCoefficient 9 62 1 2) v889_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v889_mb : Scalar.QComplex := ((-636841449808169074179879 : Int)/10^30,(-431477004613604242876599045 : Int)/10^30)
theorem v889_mb_checked : Scalar.distance (sourceCoefficient 9 62 3 1) v889_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v889_mg : Scalar.QComplex := ((-93086323498702667413335 : Int)/10^30,(137391398800762274176 : Int)/10^30)
theorem v889_mg_checked : Scalar.distance (sourceCoefficient 9 62 3 2) v889_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v889_upper : Scalar.QComplex := ((999997264749221754601450716780 : Int)/10^30,(-2338908735905267682599103159 : Int)/10^30)
theorem v889_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 62 5) 1) 14) v889_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material889 : Material (9 : Basis) (62 : Basis) where
  plus := ![v889_pa,v889_pb,v889_pg]
  minus := ![(Primitive.Addresses.material889 1).one,v889_mb,v889_mg]
  upper := v889_upper
  lower := (Primitive.Addresses.material889 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v889_pa_checked.trans (by decide +kernel)
    · exact v889_pb_checked.trans (by decide +kernel)
    · exact v889_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 62 Primitive.Addresses.material889
    · exact v889_mb_checked.trans (by decide +kernel)
    · exact v889_mg_checked.trans (by decide +kernel)
  upper_error := v889_upper_checked
  lower_error := reuse_lower_error 9 62 Primitive.Addresses.material889

def v890_pa : Scalar.QComplex := ((999999796608198881512267102392 : Int)/10^30,(-637795861439027137540489100 : Int)/10^30)
theorem v890_pa_checked : Scalar.distance (sourceCoefficient 9 63 1 0) v890_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v890_pb : Scalar.QComplex := ((-275194545741328419859853 : Int)/10^30,(-431477383920470162428579178 : Int)/10^30)
theorem v890_pb_checked : Scalar.distance (sourceCoefficient 9 63 1 1) v890_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v890_pg : Scalar.QComplex := ((-93086405643712700458036 : Int)/10^30,(59370136351193424358 : Int)/10^30)
theorem v890_pg_checked : Scalar.distance (sourceCoefficient 9 63 1 2) v890_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v890_mb : Scalar.QComplex := ((-647539992577203611438261 : Int)/10^30,(-431476985781221965705408186 : Int)/10^30)
theorem v890_mb_checked : Scalar.distance (sourceCoefficient 9 63 3 1) v890_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v890_mg : Scalar.QComplex := ((-93086319749635881001549 : Int)/10^30,(139699489859423464372 : Int)/10^30)
theorem v890_mg_checked : Scalar.distance (sourceCoefficient 9 63 3 2) v890_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v890_upper : Scalar.QComplex := ((999997206448173606210933278114 : Int)/10^30,(-2363703841189875332256802342 : Int)/10^30)
theorem v890_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 63 5) 1) 14) v890_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material890 : Material (9 : Basis) (63 : Basis) where
  plus := ![v890_pa,v890_pb,v890_pg]
  minus := ![(Primitive.Addresses.material890 1).one,v890_mb,v890_mg]
  upper := v890_upper
  lower := (Primitive.Addresses.material890 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v890_pa_checked.trans (by decide +kernel)
    · exact v890_pb_checked.trans (by decide +kernel)
    · exact v890_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 63 Primitive.Addresses.material890
    · exact v890_mb_checked.trans (by decide +kernel)
    · exact v890_mg_checked.trans (by decide +kernel)
  upper_error := v890_upper_checked
  lower_error := reuse_lower_error 9 63 Primitive.Addresses.material890

def v891_pa : Scalar.QComplex := ((999999773378553834499140098255 : Int)/10^30,(-673233125279588316886752034 : Int)/10^30)
theorem v891_pa_checked : Scalar.distance (sourceCoefficient 9 64 1 0) v891_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v891_pb : Scalar.QComplex := ((-290484923844007318572782 : Int)/10^30,(-431477369586141139788907037 : Int)/10^30)
theorem v891_pb_checked : Scalar.distance (sourceCoefficient 9 64 1 1) v891_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v891_pg : Scalar.QComplex := ((-93086403016295071149505 : Int)/10^30,(62668864225804267818 : Int)/10^30)
theorem v891_pg_checked : Scalar.distance (sourceCoefficient 9 64 1 2) v891_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v891_mb : Scalar.QComplex := ((-662830352616695585398444 : Int)/10^30,(-431476958251990630845393995 : Int)/10^30)
theorem v891_mb_checked : Scalar.distance (sourceCoefficient 9 64 3 1) v891_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v891_mg : Scalar.QComplex := ((-93086314275565643399847 : Int)/10^30,(142998214238424081206 : Int)/10^30)
theorem v891_mg_checked : Scalar.distance (sourceCoefficient 9 64 3 2) v891_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v891_upper : Scalar.QComplex := ((999997122057060611679399197177 : Int)/10^30,(-2399141012158534800307462999 : Int)/10^30)
theorem v891_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 64 5) 1) 14) v891_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material891 : Material (9 : Basis) (64 : Basis) where
  plus := ![v891_pa,v891_pb,v891_pg]
  minus := ![(Primitive.Addresses.material891 1).one,v891_mb,v891_mg]
  upper := v891_upper
  lower := (Primitive.Addresses.material891 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v891_pa_checked.trans (by decide +kernel)
    · exact v891_pb_checked.trans (by decide +kernel)
    · exact v891_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 64 Primitive.Addresses.material891
    · exact v891_mb_checked.trans (by decide +kernel)
    · exact v891_mg_checked.trans (by decide +kernel)
  upper_error := v891_upper_checked
  lower_error := reuse_lower_error 9 64 Primitive.Addresses.material891

def v892_pa : Scalar.QComplex := ((999999748517835918722752751013 : Int)/10^30,(-709199735560635727099650333 : Int)/10^30)
theorem v892_pa_checked : Scalar.distance (sourceCoefficient 9 65 1 0) v892_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v892_pb : Scalar.QComplex := ((-306003702523696892526932 : Int)/10^30,(-431477354298957746691499146 : Int)/10^30)
theorem v892_pb_checked : Scalar.distance (sourceCoefficient 9 65 1 1) v892_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v892_pg : Scalar.QComplex := ((-93086400210178250117222 : Int)/10^30,(66016867015414503853 : Int)/10^30)
theorem v892_pg_checked : Scalar.distance (sourceCoefficient 9 65 1 2) v892_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v892_mb : Scalar.QComplex := ((-678349112325883854619478 : Int)/10^30,(-431476929572805869138786371 : Int)/10^30)
theorem v892_mb_checked : Scalar.distance (sourceCoefficient 9 65 3 1) v892_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v892_mg : Scalar.QComplex := ((-93086308580274248227583 : Int)/10^30,(146346213359867433643 : Int)/10^30)
theorem v892_mg_checked : Scalar.distance (sourceCoefficient 9 65 3 2) v892_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v892_upper : Scalar.QComplex := ((999997035121273243330763191087 : Int)/10^30,(-2435107525964197355810813236 : Int)/10^30)
theorem v892_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 65 5) 1) 14) v892_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material892 : Material (9 : Basis) (65 : Basis) where
  plus := ![v892_pa,v892_pb,v892_pg]
  minus := ![(Primitive.Addresses.material892 1).one,v892_mb,v892_mg]
  upper := v892_upper
  lower := (Primitive.Addresses.material892 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v892_pa_checked.trans (by decide +kernel)
    · exact v892_pb_checked.trans (by decide +kernel)
    · exact v892_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 65 Primitive.Addresses.material892
    · exact v892_mb_checked.trans (by decide +kernel)
    · exact v892_mg_checked.trans (by decide +kernel)
  upper_error := v892_upper_checked
  lower_error := reuse_lower_error 9 65 Primitive.Addresses.material892

def v893_pa : Scalar.QComplex := ((999999735890077185143915619978 : Int)/10^30,(-726787297546992657599796188 : Int)/10^30)
theorem v893_pa_checked : Scalar.distance (sourceCoefficient 9 66 1 0) v893_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v893_pb : Scalar.QComplex := ((-313592337476585903971694 : Int)/10^30,(-431477346552636454810457185 : Int)/10^30)
theorem v893_pb_checked : Scalar.distance (sourceCoefficient 9 66 1 1) v893_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v893_pg : Scalar.QComplex := ((-93086398786850840687314 : Int)/10^30,(67654030080777641052 : Int)/10^30)
theorem v893_pg_checked : Scalar.distance (sourceCoefficient 9 66 1 2) v893_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v893_mb : Scalar.QComplex := ((-685937737768450861819732 : Int)/10^30,(-431476915277837276654798142 : Int)/10^30)
theorem v893_mb_checked : Scalar.distance (sourceCoefficient 9 66 3 1) v893_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v893_mg : Scalar.QComplex := ((-93086305744149378446420 : Int)/10^30,(147983374587372489508 : Int)/10^30)
theorem v893_mg_checked : Scalar.distance (sourceCoefficient 9 66 3 2) v893_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v893_upper : Scalar.QComplex := ((999996992138996860022933804239 : Int)/10^30,(-2452695039961580694956866431 : Int)/10^30)
theorem v893_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 66 5) 1) 14) v893_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material893 : Material (9 : Basis) (66 : Basis) where
  plus := ![v893_pa,v893_pb,v893_pg]
  minus := ![(Primitive.Addresses.material893 1).one,v893_mb,v893_mg]
  upper := v893_upper
  lower := (Primitive.Addresses.material893 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v893_pa_checked.trans (by decide +kernel)
    · exact v893_pb_checked.trans (by decide +kernel)
    · exact v893_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 66 Primitive.Addresses.material893
    · exact v893_mb_checked.trans (by decide +kernel)
    · exact v893_mg_checked.trans (by decide +kernel)
  upper_error := v893_upper_checked
  lower_error := reuse_lower_error 9 66 Primitive.Addresses.material893

def v894_pa : Scalar.QComplex := ((999999714001752771736683916300 : Int)/10^30,(-756304444427989074691593140 : Int)/10^30)
theorem v894_pa_checked : Scalar.distance (sourceCoefficient 9 67 1 0) v894_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v894_pb : Scalar.QComplex := ((-326328318062166907457396 : Int)/10^30,(-431477333152061097983303733 : Int)/10^30)
theorem v894_pb_checked : Scalar.distance (sourceCoefficient 9 67 1 1) v894_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v894_pg : Scalar.QComplex := ((-93086396322586018251984 : Int)/10^30,(70401675389312787081 : Int)/10^30)
theorem v894_pg_checked : Scalar.distance (sourceCoefficient 9 67 1 2) v894_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v894_mb : Scalar.QComplex := ((-698673702047751236794164 : Int)/10^30,(-431476890886689271390152299 : Int)/10^30)
theorem v894_mb_checked : Scalar.distance (sourceCoefficient 9 67 3 1) v894_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v894_mg : Scalar.QComplex := ((-93086300908791321654579 : Int)/10^30,(150731016746284158181 : Int)/10^30)
theorem v894_mg_checked : Scalar.distance (sourceCoefficient 9 67 3 2) v894_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v894_upper : Scalar.QComplex := ((999996919306787304751333143918 : Int)/10^30,(-2482212105102991916182141859 : Int)/10^30)
theorem v894_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 67 5) 1) 14) v894_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material894 : Material (9 : Basis) (67 : Basis) where
  plus := ![v894_pa,v894_pb,v894_pg]
  minus := ![(Primitive.Addresses.material894 1).one,v894_mb,v894_mg]
  upper := v894_upper
  lower := (Primitive.Addresses.material894 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v894_pa_checked.trans (by decide +kernel)
    · exact v894_pb_checked.trans (by decide +kernel)
    · exact v894_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 67 Primitive.Addresses.material894
    · exact v894_mb_checked.trans (by decide +kernel)
    · exact v894_mg_checked.trans (by decide +kernel)
  upper_error := v894_upper_checked
  lower_error := reuse_lower_error 9 67 Primitive.Addresses.material894

def v895_pa : Scalar.QComplex := ((999999675615098410884069180795 : Int)/10^30,(-805462412501457129700624541 : Int)/10^30)
theorem v895_pa_checked : Scalar.distance (sourceCoefficient 9 68 1 0) v895_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v895_pb : Scalar.QComplex := ((-347538867564840085034385 : Int)/10^30,(-431477309722196395127001114 : Int)/10^30)
theorem v895_pb_checked : Scalar.distance (sourceCoefficient 9 68 1 1) v895_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v895_pg : Scalar.QComplex := ((-93086392008582594296385 : Int)/10^30,(74977614199895299674 : Int)/10^30)
theorem v895_pg_checked : Scalar.distance (sourceCoefficient 9 68 1 2) v895_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v895_mb : Scalar.QComplex := ((-719884223433849467894613 : Int)/10^30,(-431476849153084359423978551 : Int)/10^30)
theorem v895_mb_checked : Scalar.distance (sourceCoefficient 9 68 3 1) v895_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v895_mg : Scalar.QComplex := ((-93086292645960403100417 : Int)/10^30,(155306950130244861487 : Int)/10^30)
theorem v895_mg_checked : Scalar.distance (sourceCoefficient 9 68 3 2) v895_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v895_upper : Scalar.QComplex := ((999996796077996797532641632965 : Int)/10^30,(-2531369933709558009575864484 : Int)/10^30)
theorem v895_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 68 5) 1) 14) v895_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material895 : Material (9 : Basis) (68 : Basis) where
  plus := ![v895_pa,v895_pb,v895_pg]
  minus := ![(Primitive.Addresses.material895 1).one,v895_mb,v895_mg]
  upper := v895_upper
  lower := (Primitive.Addresses.material895 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v895_pa_checked.trans (by decide +kernel)
    · exact v895_pb_checked.trans (by decide +kernel)
    · exact v895_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 68 Primitive.Addresses.material895
    · exact v895_mb_checked.trans (by decide +kernel)
    · exact v895_mg_checked.trans (by decide +kernel)
  upper_error := v895_upper_checked
  lower_error := reuse_lower_error 9 68 Primitive.Addresses.material895

def v896_pa : Scalar.QComplex := ((999999657954561858934027142319 : Int)/10^30,(-827097793061407093851236152 : Int)/10^30)
theorem v896_pa_checked : Scalar.distance (sourceCoefficient 9 69 1 0) v896_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v896_pb : Scalar.QComplex := ((-356874043801055171143589 : Int)/10^30,(-431477298969676649887028388 : Int)/10^30)
theorem v896_pb_checked : Scalar.distance (sourceCoefficient 9 69 1 1) v896_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v896_pg : Scalar.QComplex := ((-93086390026736742153554 : Int)/10^30,(76991574089784027826 : Int)/10^30)
theorem v896_pg_checked : Scalar.distance (sourceCoefficient 9 69 1 2) v896_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v896_mb : Scalar.QComplex := ((-729219386915211538000647 : Int)/10^30,(-431476830344731966715087680 : Int)/10^30)
theorem v896_mb_checked : Scalar.distance (sourceCoefficient 9 69 3 1) v896_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v896_mg : Scalar.QComplex := ((-93086288926158609301698 : Int)/10^30,(157320907560000568744 : Int)/10^30)
theorem v896_mg_checked : Scalar.distance (sourceCoefficient 9 69 3 2) v896_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v896_upper : Scalar.QComplex := ((999996741076782448795868494562 : Int)/10^30,(-2553005251565666162705030364 : Int)/10^30)
theorem v896_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 69 5) 1) 14) v896_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material896 : Material (9 : Basis) (69 : Basis) where
  plus := ![v896_pa,v896_pb,v896_pg]
  minus := ![(Primitive.Addresses.material896 1).one,v896_mb,v896_mg]
  upper := v896_upper
  lower := (Primitive.Addresses.material896 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v896_pa_checked.trans (by decide +kernel)
    · exact v896_pb_checked.trans (by decide +kernel)
    · exact v896_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 69 Primitive.Addresses.material896
    · exact v896_mb_checked.trans (by decide +kernel)
    · exact v896_mg_checked.trans (by decide +kernel)
  upper_error := v896_upper_checked
  lower_error := reuse_lower_error 9 69 Primitive.Addresses.material896

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
