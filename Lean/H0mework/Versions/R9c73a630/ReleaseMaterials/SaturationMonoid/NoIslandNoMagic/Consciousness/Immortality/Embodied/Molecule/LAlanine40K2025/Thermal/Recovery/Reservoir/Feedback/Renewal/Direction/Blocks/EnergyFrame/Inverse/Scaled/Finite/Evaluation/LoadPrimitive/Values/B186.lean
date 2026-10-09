import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B124

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2977_pa : Scalar.QComplex := ((999998478089766123939893610874 : Int)/10^30,(-1744654163879294513316425880 : Int)/10^30)
theorem v2977_pa_checked : Scalar.distance (sourceCoefficient 37 92 1 0) v2977_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2977_pb : Scalar.QComplex := ((-752778939500764648261910 : Int)/10^30,(-431476798911806794441584874 : Int)/10^30)
theorem v2977_pb_checked : Scalar.distance (sourceCoefficient 37 92 1 1) v2977_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2977_pg : Scalar.QComplex := ((-93086281171100945498006 : Int)/10^30,(162403615208924041086 : Int)/10^30)
theorem v2977_pg_checked : Scalar.distance (sourceCoefficient 37 92 1 2) v2977_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2977_mb : Scalar.QComplex := ((-1125123703674014683695842 : Int)/10^30,(-431475988638954211407480506 : Int)/10^30)
theorem v2977_mb_checked : Scalar.distance (sourceCoefficient 37 92 3 1) v2977_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2977_mg : Scalar.QComplex := ((-93086106363818674287974 : Int)/10^30,(242732822938823133558 : Int)/10^30)
theorem v2977_mg_checked : Scalar.distance (sourceCoefficient 37 92 3 2) v2977_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2977_upper : Scalar.QComplex := ((999993977594688015869546265466 : Int)/10^30,(-3470558219451522051184113966 : Int)/10^30)
theorem v2977_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 92 5) 1) 14) v2977_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2977 : Material (37 : Basis) (92 : Basis) where
  plus := ![v2977_pa,v2977_pb,v2977_pg]
  minus := ![(Primitive.Addresses.material2977 1).one,v2977_mb,v2977_mg]
  upper := v2977_upper
  lower := (Primitive.Addresses.material2977 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2977_pa_checked.trans (by decide +kernel)
    · exact v2977_pb_checked.trans (by decide +kernel)
    · exact v2977_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 92 Primitive.Addresses.material2977
    · exact v2977_mb_checked.trans (by decide +kernel)
    · exact v2977_mg_checked.trans (by decide +kernel)
  upper_error := v2977_upper_checked
  lower_error := reuse_lower_error 37 92 Primitive.Addresses.material2977

def v2978_pa : Scalar.QComplex := ((999998411203514852935548707353 : Int)/10^30,(-1782579716596107150633525470 : Int)/10^30)
theorem v2978_pa_checked : Scalar.distance (sourceCoefficient 37 93 1 0) v2978_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2978_pb : Scalar.QComplex := ((-769142951030174990657851 : Int)/10^30,(-431476764745903477720183973 : Int)/10^30)
theorem v2978_pb_checked : Scalar.distance (sourceCoefficient 37 93 1 1) v2978_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2978_pg : Scalar.QComplex := ((-93086274372544774766805 : Int)/10^30,(165933968225303819448 : Int)/10^30)
theorem v2978_pg_checked : Scalar.distance (sourceCoefficient 37 93 1 2) v2978_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2978_mb : Scalar.QComplex := ((-1141487679626719874252575 : Int)/10^30,(-431475940351658674052489895 : Int)/10^30)
theorem v2978_mb_checked : Scalar.distance (sourceCoefficient 37 93 3 1) v2978_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2978_mg : Scalar.QComplex := ((-93086096518729383031653 : Int)/10^30,(246263168773843359080 : Int)/10^30)
theorem v2978_mg_checked : Scalar.distance (sourceCoefficient 37 93 3 2) v2978_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2978_upper : Scalar.QComplex := ((999993845252472954126985459540 : Int)/10^30,(-3508483600243077144743167553 : Int)/10^30)
theorem v2978_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 93 5) 1) 14) v2978_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2978 : Material (37 : Basis) (93 : Basis) where
  plus := ![v2978_pa,v2978_pb,v2978_pg]
  minus := ![(Primitive.Addresses.material2978 1).one,v2978_mb,v2978_mg]
  upper := v2978_upper
  lower := (Primitive.Addresses.material2978 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2978_pa_checked.trans (by decide +kernel)
    · exact v2978_pb_checked.trans (by decide +kernel)
    · exact v2978_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 93 Primitive.Addresses.material2978
    · exact v2978_mb_checked.trans (by decide +kernel)
    · exact v2978_mg_checked.trans (by decide +kernel)
  upper_error := v2978_upper_checked
  lower_error := reuse_lower_error 37 93 Primitive.Addresses.material2978

def v2979_pa : Scalar.QComplex := ((999998330343061170592376652149 : Int)/10^30,(-1827378201113420819036739821 : Int)/10^30)
theorem v2979_pa_checked : Scalar.distance (sourceCoefficient 37 94 1 0) v2979_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2979_pb : Scalar.QComplex := ((-788472474965708420954230 : Int)/10^30,(-431476723322383046807647667 : Int)/10^30)
theorem v2979_pb_checked : Scalar.distance (sourceCoefficient 37 94 1 1) v2979_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2979_pg : Scalar.QComplex := ((-93086266140709595951897 : Int)/10^30,(170104097584061889404 : Int)/10^30)
theorem v2979_pg_checked : Scalar.distance (sourceCoefficient 37 94 1 2) v2979_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2979_mb : Scalar.QComplex := ((-1160817160618355654691668 : Int)/10^30,(-431475882247645080085407779 : Int)/10^30)
theorem v2979_mb_checked : Scalar.distance (sourceCoefficient 37 94 3 1) v2979_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2979_mg : Scalar.QComplex := ((-93086084688263448351255 : Int)/10^30,(250433289476168673221 : Int)/10^30)
theorem v2979_mg_checked : Scalar.distance (sourceCoefficient 37 94 3 2) v2979_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2979_upper : Scalar.QComplex := ((999993687074019513816152544660 : Int)/10^30,(-3553281878480503071593651050 : Int)/10^30)
theorem v2979_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 94 5) 1) 14) v2979_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2979 : Material (37 : Basis) (94 : Basis) where
  plus := ![v2979_pa,v2979_pb,v2979_pg]
  minus := ![(Primitive.Addresses.material2979 1).one,v2979_mb,v2979_mg]
  upper := v2979_upper
  lower := (Primitive.Addresses.material2979 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2979_pa_checked.trans (by decide +kernel)
    · exact v2979_pb_checked.trans (by decide +kernel)
    · exact v2979_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 94 Primitive.Addresses.material2979
    · exact v2979_mb_checked.trans (by decide +kernel)
    · exact v2979_mg_checked.trans (by decide +kernel)
  upper_error := v2979_upper_checked
  lower_error := reuse_lower_error 37 94 Primitive.Addresses.material2979

def v2980_pa : Scalar.QComplex := ((999998248457208179589723369870 : Int)/10^30,(-1871652349059159270240006362 : Int)/10^30)
theorem v2980_pa_checked : Scalar.distance (sourceCoefficient 37 95 1 0) v2980_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2980_pb : Scalar.QComplex := ((-807575758528012478828916 : Int)/10^30,(-431476681249306056143093495 : Int)/10^30)
theorem v2980_pb_checked : Scalar.distance (sourceCoefficient 37 95 1 1) v2980_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2980_pg : Scalar.QComplex := ((-93086257791081767111426 : Int)/10^30,(174225418223080096278 : Int)/10^30)
theorem v2980_pg_checked : Scalar.distance (sourceCoefficient 37 95 1 2) v2980_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2980_mb : Scalar.QComplex := ((-1179920400760463637233675 : Int)/10^30,(-431475823689310420834690922 : Int)/10^30)
theorem v2980_mb_checked : Scalar.distance (sourceCoefficient 37 95 3 1) v2980_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2980_mg : Scalar.QComplex := ((-93086072782124634377248 : Int)/10^30,(254554601375278089518 : Int)/10^30)
theorem v2980_mg_checked : Scalar.distance (sourceCoefficient 37 95 3 2) v2980_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2980_upper : Scalar.QComplex := ((999993528775125647154284837254 : Int)/10^30,(-3597555819157545328457467560 : Int)/10^30)
theorem v2980_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 95 5) 1) 14) v2980_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2980 : Material (37 : Basis) (95 : Basis) where
  plus := ![v2980_pa,v2980_pb,v2980_pg]
  minus := ![(Primitive.Addresses.material2980 1).one,v2980_mb,v2980_mg]
  upper := v2980_upper
  lower := (Primitive.Addresses.material2980 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2980_pa_checked.trans (by decide +kernel)
    · exact v2980_pb_checked.trans (by decide +kernel)
    · exact v2980_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 95 Primitive.Addresses.material2980
    · exact v2980_mb_checked.trans (by decide +kernel)
    · exact v2980_mg_checked.trans (by decide +kernel)
  upper_error := v2980_upper_checked
  lower_error := reuse_lower_error 37 95 Primitive.Addresses.material2980

def v2981_pa : Scalar.QComplex := ((999998208432131231868193136669 : Int)/10^30,(-1892916408038356883253145747 : Int)/10^30)
theorem v2981_pa_checked : Scalar.distance (sourceCoefficient 37 96 1 0) v2981_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2981_pb : Scalar.QComplex := ((-816750713878239930147260 : Int)/10^30,(-431476660641505756634580226 : Int)/10^30)
theorem v2981_pb_checked : Scalar.distance (sourceCoefficient 37 96 1 1) v2981_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2981_pg : Scalar.QComplex := ((-93086253705235246367424 : Int)/10^30,(176204812684341819489 : Int)/10^30)
theorem v2981_pg_checked : Scalar.distance (sourceCoefficient 37 96 1 2) v2981_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2981_mb : Scalar.QComplex := ((-1189095334910832377883628 : Int)/10^30,(-431475795163944551955115889 : Int)/10^30)
theorem v2981_mb_checked : Scalar.distance (sourceCoefficient 37 96 3 1) v2981_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2981_mg : Scalar.QComplex := ((-93086066988151363528954 : Int)/10^30,(256533991573619264299 : Int)/10^30)
theorem v2981_mg_checked : Scalar.distance (sourceCoefficient 37 96 3 2) v2981_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2981_upper : Scalar.QComplex := ((999993452050271574349712586304 : Int)/10^30,(-3618819777386773178637136558 : Int)/10^30)
theorem v2981_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 96 5) 1) 14) v2981_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2981 : Material (37 : Basis) (96 : Basis) where
  plus := ![v2981_pa,v2981_pb,v2981_pg]
  minus := ![(Primitive.Addresses.material2981 1).one,v2981_mb,v2981_mg]
  upper := v2981_upper
  lower := (Primitive.Addresses.material2981 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2981_pa_checked.trans (by decide +kernel)
    · exact v2981_pb_checked.trans (by decide +kernel)
    · exact v2981_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 96 Primitive.Addresses.material2981
    · exact v2981_mb_checked.trans (by decide +kernel)
    · exact v2981_mg_checked.trans (by decide +kernel)
  upper_error := v2981_upper_checked
  lower_error := reuse_lower_error 37 96 Primitive.Addresses.material2981

def v2982_pa : Scalar.QComplex := ((999998067265807754121127808559 : Int)/10^30,(-1966078495134489758262404211 : Int)/10^30)
theorem v2982_pa_checked : Scalar.distance (sourceCoefficient 37 97 1 0) v2982_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2982_pb : Scalar.QComplex := ((-848318479903707019035238 : Int)/10^30,(-431476587750147693421476943 : Int)/10^30)
theorem v2982_pb_checked : Scalar.distance (sourceCoefficient 37 97 1 1) v2982_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2982_pg : Scalar.QComplex := ((-93086239272154679546622 : Int)/10^30,(183015206945675078449 : Int)/10^30)
theorem v2982_pg_checked : Scalar.distance (sourceCoefficient 37 97 1 2) v2982_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2982_mb : Scalar.QComplex := ((-1220663026280218353658221 : Int)/10^30,(-431475695031053308951418578 : Int)/10^30)
theorem v2982_mb_checked : Scalar.distance (sourceCoefficient 37 97 3 1) v2982_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2982_mg : Scalar.QComplex := ((-93086046678012652044292 : Int)/10^30,(263344370844033002023 : Int)/10^30)
theorem v2982_mg_checked : Scalar.distance (sourceCoefficient 37 97 3 2) v2982_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2982_upper : Scalar.QComplex := ((999993184613033232027864769180 : Int)/10^30,(-3691981511876303732653499557 : Int)/10^30)
theorem v2982_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 97 5) 1) 14) v2982_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2982 : Material (37 : Basis) (97 : Basis) where
  plus := ![v2982_pa,v2982_pb,v2982_pg]
  minus := ![(Primitive.Addresses.material2982 1).one,v2982_mb,v2982_mg]
  upper := v2982_upper
  lower := (Primitive.Addresses.material2982 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2982_pa_checked.trans (by decide +kernel)
    · exact v2982_pb_checked.trans (by decide +kernel)
    · exact v2982_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 97 Primitive.Addresses.material2982
    · exact v2982_mb_checked.trans (by decide +kernel)
    · exact v2982_mg_checked.trans (by decide +kernel)
  upper_error := v2982_upper_checked
  lower_error := reuse_lower_error 37 97 Primitive.Addresses.material2982

def v2983_pa : Scalar.QComplex := ((999999637904075902926834807127 : Int)/10^30,(-850994545858366875275082891 : Int)/10^30)
theorem v2983_pa_checked : Scalar.distance (sourceCoefficient 38 39 1 0) v2983_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2983_pb : Scalar.QComplex := ((-367185017020862375150346 : Int)/10^30,(-431477364751261061312888102 : Int)/10^30)
theorem v2983_pb_checked : Scalar.distance (sourceCoefficient 38 39 1 1) v2983_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2983_pg : Scalar.QComplex := ((-93086396189341800894047 : Int)/10^30,(79216044134547642943 : Int)/10^30)
theorem v2983_pg_checked : Scalar.distance (sourceCoefficient 38 39 1 2) v2983_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2983_mb : Scalar.QComplex := ((-739530413062316831996512 : Int)/10^30,(-431476887228386384951977340 : Int)/10^30)
theorem v2983_mb_checked : Scalar.distance (sourceCoefficient 38 39 3 1) v2983_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2983_mg : Scalar.QComplex := ((-93086293169143911203404 : Int)/10^30,(159545382094542935156 : Int)/10^30)
theorem v2983_mg_checked : Scalar.distance (sourceCoefficient 38 39 3 2) v2983_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2983_upper : Scalar.QComplex := ((999996679782698924558691608462 : Int)/10^30,(-2576901934165899968638053441 : Int)/10^30)
theorem v2983_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 39 5) 1) 14) v2983_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2983 : Material (38 : Basis) (39 : Basis) where
  plus := ![v2983_pa,v2983_pb,v2983_pg]
  minus := ![(Primitive.Addresses.material2983 1).one,v2983_mb,v2983_mg]
  upper := v2983_upper
  lower := (Primitive.Addresses.material2983 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2983_pa_checked.trans (by decide +kernel)
    · exact v2983_pb_checked.trans (by decide +kernel)
    · exact v2983_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 39 Primitive.Addresses.material2983
    · exact v2983_mb_checked.trans (by decide +kernel)
    · exact v2983_mg_checked.trans (by decide +kernel)
  upper_error := v2983_upper_checked
  lower_error := reuse_lower_error 38 39 Primitive.Addresses.material2983

def v2984_pa : Scalar.QComplex := ((999999618297839201772892101282 : Int)/10^30,(-873730036052277796341591583 : Int)/10^30)
theorem v2984_pa_checked : Scalar.distance (sourceCoefficient 38 40 1 0) v2984_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2984_pb : Scalar.QComplex := ((-376994869897068730513201 : Int)/10^30,(-431477356210237455544674514 : Int)/10^30)
theorem v2984_pb_checked : Scalar.distance (sourceCoefficient 38 40 1 1) v2984_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2984_pg : Scalar.QComplex := ((-93086394355489545925602 : Int)/10^30,(81332409740954970375 : Int)/10^30)
theorem v2984_pg_checked : Scalar.distance (sourceCoefficient 38 40 1 2) v2984_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2984_mb : Scalar.QComplex := ((-749340254915347930768714 : Int)/10^30,(-431476870221904746603549853 : Int)/10^30)
theorem v2984_mb_checked : Scalar.distance (sourceCoefficient 38 40 3 1) v2984_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2984_mg : Scalar.QComplex := ((-93086289508964138301000 : Int)/10^30,(161661745330398722238 : Int)/10^30)
theorem v2984_mg_checked : Scalar.distance (sourceCoefficient 38 40 3 2) v2984_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2984_upper : Scalar.QComplex := ((999996620937097897459609419802 : Int)/10^30,(-2599637356659383061866407822 : Int)/10^30)
theorem v2984_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 40 5) 1) 14) v2984_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2984 : Material (38 : Basis) (40 : Basis) where
  plus := ![v2984_pa,v2984_pb,v2984_pg]
  minus := ![(Primitive.Addresses.material2984 1).one,v2984_mb,v2984_mg]
  upper := v2984_upper
  lower := (Primitive.Addresses.material2984 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2984_pa_checked.trans (by decide +kernel)
    · exact v2984_pb_checked.trans (by decide +kernel)
    · exact v2984_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 40 Primitive.Addresses.material2984
    · exact v2984_mb_checked.trans (by decide +kernel)
    · exact v2984_mg_checked.trans (by decide +kernel)
  upper_error := v2984_upper_checked
  lower_error := reuse_lower_error 38 40 Primitive.Addresses.material2984

def v2985_pa : Scalar.QComplex := ((999999605537845283596363461308 : Int)/10^30,(-888214024789304804393868740 : Int)/10^30)
theorem v2985_pa_checked : Scalar.distance (sourceCoefficient 38 41 1 0) v2985_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2985_pb : Scalar.QComplex := ((-383244385369674857689225 : Int)/10^30,(-431477350613979582894731406 : Int)/10^30)
theorem v2985_pb_checked : Scalar.distance (sourceCoefficient 38 41 1 1) v2985_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2985_pg : Scalar.QComplex := ((-93086393157933509801508 : Int)/10^30,(82680672534323968899 : Int)/10^30)
theorem v2985_pg_checked : Scalar.distance (sourceCoefficient 38 41 1 2) v2985_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2985_mb : Scalar.QComplex := ((-755589763231655332527906 : Int)/10^30,(-431476859232598572565399565 : Int)/10^30)
theorem v2985_mb_checked : Scalar.distance (sourceCoefficient 38 41 3 1) v2985_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2985_mg : Scalar.QComplex := ((-93086287147918480906354 : Int)/10^30,(163010006588310940884 : Int)/10^30)
theorem v2985_mg_checked : Scalar.distance (sourceCoefficient 38 41 3 2) v2985_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2985_upper : Scalar.QComplex := ((999996583179072400880508363245 : Int)/10^30,(-2614121301801618329784528166 : Int)/10^30)
theorem v2985_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 41 5) 1) 14) v2985_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2985 : Material (38 : Basis) (41 : Basis) where
  plus := ![v2985_pa,v2985_pb,v2985_pg]
  minus := ![(Primitive.Addresses.material2985 1).one,v2985_mb,v2985_mg]
  upper := v2985_upper
  lower := (Primitive.Addresses.material2985 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2985_pa_checked.trans (by decide +kernel)
    · exact v2985_pb_checked.trans (by decide +kernel)
    · exact v2985_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 41 Primitive.Addresses.material2985
    · exact v2985_mb_checked.trans (by decide +kernel)
    · exact v2985_mg_checked.trans (by decide +kernel)
  upper_error := v2985_upper_checked
  lower_error := reuse_lower_error 38 41 Primitive.Addresses.material2985

def v2986_pa : Scalar.QComplex := ((999999595092009731041390955592 : Int)/10^30,(-899897670064456070009371905 : Int)/10^30)
theorem v2986_pa_checked : Scalar.distance (sourceCoefficient 38 42 1 0) v2986_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2986_pb : Scalar.QComplex := ((-388285615581527030975262 : Int)/10^30,(-431477346011760916651467373 : Int)/10^30)
theorem v2986_pb_checked : Scalar.distance (sourceCoefficient 38 42 1 1) v2986_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2986_pg : Scalar.QComplex := ((-93086392175312242047508 : Int)/10^30,(83768261351708053397 : Int)/10^30)
theorem v2986_pg_checked : Scalar.distance (sourceCoefficient 38 42 1 2) v2986_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2986_mb : Scalar.QComplex := ((-760630987594919669605259 : Int)/10^30,(-431476850280026995690353551 : Int)/10^30)
theorem v2986_mb_checked : Scalar.distance (sourceCoefficient 38 42 3 1) v2986_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2986_mg : Scalar.QComplex := ((-93086285226757412806688 : Int)/10^30,(164097594152778104953 : Int)/10^30)
theorem v2986_mg_checked : Scalar.distance (sourceCoefficient 38 42 3 2) v2986_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2986_upper : Scalar.QComplex := ((999996552568340593279080059955 : Int)/10^30,(-2625804911646787890535010530 : Int)/10^30)
theorem v2986_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 42 5) 1) 14) v2986_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2986 : Material (38 : Basis) (42 : Basis) where
  plus := ![v2986_pa,v2986_pb,v2986_pg]
  minus := ![(Primitive.Addresses.material2986 1).one,v2986_mb,v2986_mg]
  upper := v2986_upper
  lower := (Primitive.Addresses.material2986 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2986_pa_checked.trans (by decide +kernel)
    · exact v2986_pb_checked.trans (by decide +kernel)
    · exact v2986_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 42 Primitive.Addresses.material2986
    · exact v2986_mb_checked.trans (by decide +kernel)
    · exact v2986_mg_checked.trans (by decide +kernel)
  upper_error := v2986_upper_checked
  lower_error := reuse_lower_error 38 42 Primitive.Addresses.material2986

def v2987_pa : Scalar.QComplex := ((999999581043803005806597516120 : Int)/10^30,(-915375452185654695214561562 : Int)/10^30)
theorem v2987_pa_checked : Scalar.distance (sourceCoefficient 38 43 1 0) v2987_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2987_pb : Scalar.QComplex := ((-394963930494467756027315 : Int)/10^30,(-431477339794093246204628615 : Int)/10^30)
theorem v2987_pb_checked : Scalar.distance (sourceCoefficient 38 43 1 1) v2987_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2987_pg : Scalar.QComplex := ((-93086390850767547519213 : Int)/10^30,(85209032816204272110 : Int)/10^30)
theorem v2987_pg_checked : Scalar.distance (sourceCoefficient 38 43 1 2) v2987_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2987_mb : Scalar.QComplex := ((-767309294655651372261007 : Int)/10^30,(-431476838299276650635699513 : Int)/10^30)
theorem v2987_mb_checked : Scalar.distance (sourceCoefficient 38 43 3 1) v2987_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2987_mg : Scalar.QComplex := ((-93086282658892327544615 : Int)/10^30,(165538363937786844825 : Int)/10^30)
theorem v2987_mg_checked : Scalar.distance (sourceCoefficient 38 43 3 2) v2987_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2987_upper : Scalar.QComplex := ((999996511806906983434705221997 : Int)/10^30,(-2641282646469717829824190065 : Int)/10^30)
theorem v2987_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 43 5) 1) 14) v2987_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2987 : Material (38 : Basis) (43 : Basis) where
  plus := ![v2987_pa,v2987_pb,v2987_pg]
  minus := ![(Primitive.Addresses.material2987 1).one,v2987_mb,v2987_mg]
  upper := v2987_upper
  lower := (Primitive.Addresses.material2987 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2987_pa_checked.trans (by decide +kernel)
    · exact v2987_pb_checked.trans (by decide +kernel)
    · exact v2987_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 43 Primitive.Addresses.material2987
    · exact v2987_mb_checked.trans (by decide +kernel)
    · exact v2987_mg_checked.trans (by decide +kernel)
  upper_error := v2987_upper_checked
  lower_error := reuse_lower_error 38 43 Primitive.Addresses.material2987

def v2988_pa : Scalar.QComplex := ((999999575666421197197099557530 : Int)/10^30,(-921231229142075763407612494 : Int)/10^30)
theorem v2988_pa_checked : Scalar.distance (sourceCoefficient 38 44 1 0) v2988_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2988_pb : Scalar.QComplex := ((-397490566553890904427548 : Int)/10^30,(-431477337405801064258425949 : Int)/10^30)
theorem v2988_pb_checked : Scalar.distance (sourceCoefficient 38 44 1 1) v2988_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2988_pg : Scalar.QComplex := ((-93086390342863300694286 : Int)/10^30,(85754126180310269047 : Int)/10^30)
theorem v2988_pg_checked : Scalar.distance (sourceCoefficient 38 44 1 2) v2988_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2988_mb : Scalar.QComplex := ((-769835927713303854432918 : Int)/10^30,(-431476833730612234141479698 : Int)/10^30)
theorem v2988_mb_checked : Scalar.distance (sourceCoefficient 38 44 3 1) v2988_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2988_mg : Scalar.QComplex := ((-93086281680597246705953 : Int)/10^30,(166083456660631180456 : Int)/10^30)
theorem v2988_mg_checked : Scalar.distance (sourceCoefficient 38 44 3 2) v2988_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2988_upper : Scalar.QComplex := ((999996496322993388956706215618 : Int)/10^30,(-2647138405423773819916391396 : Int)/10^30)
theorem v2988_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 44 5) 1) 14) v2988_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2988 : Material (38 : Basis) (44 : Basis) where
  plus := ![v2988_pa,v2988_pb,v2988_pg]
  minus := ![(Primitive.Addresses.material2988 1).one,v2988_mb,v2988_mg]
  upper := v2988_upper
  lower := (Primitive.Addresses.material2988 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2988_pa_checked.trans (by decide +kernel)
    · exact v2988_pb_checked.trans (by decide +kernel)
    · exact v2988_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 44 Primitive.Addresses.material2988
    · exact v2988_mb_checked.trans (by decide +kernel)
    · exact v2988_mg_checked.trans (by decide +kernel)
  upper_error := v2988_upper_checked
  lower_error := reuse_lower_error 38 44 Primitive.Addresses.material2988

def v2989_pa : Scalar.QComplex := ((999999572978332937146050265271 : Int)/10^30,(-924144551343675757501955046 : Int)/10^30)
theorem v2989_pa_checked : Scalar.distance (sourceCoefficient 38 45 1 0) v2989_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2989_pb : Scalar.QComplex := ((-398747599560847902655050 : Int)/10^30,(-431477336210247156998566512 : Int)/10^30)
theorem v2989_pb_checked : Scalar.distance (sourceCoefficient 38 45 1 1) v2989_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2989_pg : Scalar.QComplex := ((-93086390088787366006976 : Int)/10^30,(86025316939479035227 : Int)/10^30)
theorem v2989_pg_checked : Scalar.distance (sourceCoefficient 38 45 1 2) v2989_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2989_mb : Scalar.QComplex := ((-771092959220500838707738 : Int)/10^30,(-431476831450295901702088166 : Int)/10^30)
theorem v2989_mb_checked : Scalar.distance (sourceCoefficient 38 45 3 1) v2989_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2989_mg : Scalar.QComplex := ((-93086281192495995438469 : Int)/10^30,(166354647099567144488 : Int)/10^30)
theorem v2989_mg_checked : Scalar.distance (sourceCoefficient 38 45 3 2) v2989_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2989_upper : Scalar.QComplex := ((999996488606779307061339051423 : Int)/10^30,(-2650051718646926142207087374 : Int)/10^30)
theorem v2989_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 45 5) 1) 14) v2989_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2989 : Material (38 : Basis) (45 : Basis) where
  plus := ![v2989_pa,v2989_pb,v2989_pg]
  minus := ![(Primitive.Addresses.material2989 1).one,v2989_mb,v2989_mg]
  upper := v2989_upper
  lower := (Primitive.Addresses.material2989 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2989_pa_checked.trans (by decide +kernel)
    · exact v2989_pb_checked.trans (by decide +kernel)
    · exact v2989_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 45 Primitive.Addresses.material2989
    · exact v2989_mb_checked.trans (by decide +kernel)
    · exact v2989_mg_checked.trans (by decide +kernel)
  upper_error := v2989_upper_checked
  lower_error := reuse_lower_error 38 45 Primitive.Addresses.material2989

def v2990_pa : Scalar.QComplex := ((999999557721512542554795852236 : Int)/10^30,(-940508787468054410336380660 : Int)/10^30)
theorem v2990_pa_checked : Scalar.distance (sourceCoefficient 38 46 1 0) v2990_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2990_pb : Scalar.QComplex := ((-405808399378067599575277 : Int)/10^30,(-431477329404034221031654050 : Int)/10^30)
theorem v2990_pb_checked : Scalar.distance (sourceCoefficient 38 46 1 1) v2990_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2990_pg : Scalar.QComplex := ((-93086388644503889743336 : Int)/10^30,(87548605234687124513 : Int)/10^30)
theorem v2990_pg_checked : Scalar.distance (sourceCoefficient 38 46 1 2) v2990_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2990_mb : Scalar.QComplex := ((-778153750535206845895867 : Int)/10^30,(-431476818550933264357519608 : Int)/10^30)
theorem v2990_mb_checked : Scalar.distance (sourceCoefficient 38 46 3 1) v2990_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2990_mg : Scalar.QComplex := ((-93086278433683864541022 : Int)/10^30,(167877933581233791852 : Int)/10^30)
theorem v2990_mg_checked : Scalar.distance (sourceCoefficient 38 46 3 2) v2990_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2990_upper : Scalar.QComplex := ((999996445106794636938836132251 : Int)/10^30,(-2666415904066809452857148925 : Int)/10^30)
theorem v2990_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 46 5) 1) 14) v2990_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2990 : Material (38 : Basis) (46 : Basis) where
  plus := ![v2990_pa,v2990_pb,v2990_pg]
  minus := ![(Primitive.Addresses.material2990 1).one,v2990_mb,v2990_mg]
  upper := v2990_upper
  lower := (Primitive.Addresses.material2990 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2990_pa_checked.trans (by decide +kernel)
    · exact v2990_pb_checked.trans (by decide +kernel)
    · exact v2990_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 46 Primitive.Addresses.material2990
    · exact v2990_mb_checked.trans (by decide +kernel)
    · exact v2990_mg_checked.trans (by decide +kernel)
  upper_error := v2990_upper_checked
  lower_error := reuse_lower_error 38 46 Primitive.Addresses.material2990

def v2991_pa : Scalar.QComplex := ((999999554009994687744978935447 : Int)/10^30,(-944446828422556143904635835 : Int)/10^30)
theorem v2991_pa_checked : Scalar.distance (sourceCoefficient 38 47 1 0) v2991_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2991_pb : Scalar.QComplex := ((-407507575467541027601025 : Int)/10^30,(-431477327743126142676637614 : Int)/10^30)
theorem v2991_pb_checked : Scalar.distance (sourceCoefficient 38 47 1 1) v2991_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2991_pg : Scalar.QComplex := ((-93086388292596783095750 : Int)/10^30,(87915183401546705248 : Int)/10^30)
theorem v2991_pg_checked : Scalar.distance (sourceCoefficient 38 47 1 2) v2991_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2991_mb : Scalar.QComplex := ((-779852924558710492529671 : Int)/10^30,(-431476815423713367269134731 : Int)/10^30)
theorem v2991_mb_checked : Scalar.distance (sourceCoefficient 38 47 3 1) v2991_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2991_mg : Scalar.QComplex := ((-93086277765436440992468 : Int)/10^30,(168244511307919583886 : Int)/10^30)
theorem v2991_mg_checked : Scalar.distance (sourceCoefficient 38 47 3 2) v2991_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2991_upper : Scalar.QComplex := ((999996434598580878813545754783 : Int)/10^30,(-2670353932750318668348938400 : Int)/10^30)
theorem v2991_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 47 5) 1) 14) v2991_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2991 : Material (38 : Basis) (47 : Basis) where
  plus := ![v2991_pa,v2991_pb,v2991_pg]
  minus := ![(Primitive.Addresses.material2991 1).one,v2991_mb,v2991_mg]
  upper := v2991_upper
  lower := (Primitive.Addresses.material2991 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2991_pa_checked.trans (by decide +kernel)
    · exact v2991_pb_checked.trans (by decide +kernel)
    · exact v2991_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 47 Primitive.Addresses.material2991
    · exact v2991_mb_checked.trans (by decide +kernel)
    · exact v2991_mg_checked.trans (by decide +kernel)
  upper_error := v2991_upper_checked
  lower_error := reuse_lower_error 38 47 Primitive.Addresses.material2991

def v2992_pa : Scalar.QComplex := ((999999527727064050824167222010 : Int)/10^30,(-971877383653218692133587441 : Int)/10^30)
theorem v2992_pa_checked : Scalar.distance (sourceCoefficient 38 48 1 0) v2992_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2992_pb : Scalar.QComplex := ((-419343242952827739160373 : Int)/10^30,(-431477315926503221636403288 : Int)/10^30)
theorem v2992_pb_checked : Scalar.distance (sourceCoefficient 38 48 1 1) v2992_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2992_pg : Scalar.QComplex := ((-93086385794652842969298 : Int)/10^30,(90468595805710699965 : Int)/10^30)
theorem v2992_pg_checked : Scalar.distance (sourceCoefficient 38 48 1 2) v2992_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2992_mb : Scalar.QComplex := ((-791688577439823902673284 : Int)/10^30,(-431476793393446864970697313 : Int)/10^30)
theorem v2992_mb_checked : Scalar.distance (sourceCoefficient 38 48 3 1) v2992_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2992_mg : Scalar.QComplex := ((-93086273064013527596810 : Int)/10^30,(170797920605718326710 : Int)/10^30)
theorem v2992_mg_checked : Scalar.distance (sourceCoefficient 38 48 3 2) v2992_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2992_upper : Scalar.QComplex := ((999996360973039539638532151972 : Int)/10^30,(-2697784401764437509388376308 : Int)/10^30)
theorem v2992_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 48 5) 1) 14) v2992_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2992 : Material (38 : Basis) (48 : Basis) where
  plus := ![v2992_pa,v2992_pb,v2992_pg]
  minus := ![(Primitive.Addresses.material2992 1).one,v2992_mb,v2992_mg]
  upper := v2992_upper
  lower := (Primitive.Addresses.material2992 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2992_pa_checked.trans (by decide +kernel)
    · exact v2992_pb_checked.trans (by decide +kernel)
    · exact v2992_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 48 Primitive.Addresses.material2992
    · exact v2992_mb_checked.trans (by decide +kernel)
    · exact v2992_mg_checked.trans (by decide +kernel)
  upper_error := v2992_upper_checked
  lower_error := reuse_lower_error 38 48 Primitive.Addresses.material2992

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
