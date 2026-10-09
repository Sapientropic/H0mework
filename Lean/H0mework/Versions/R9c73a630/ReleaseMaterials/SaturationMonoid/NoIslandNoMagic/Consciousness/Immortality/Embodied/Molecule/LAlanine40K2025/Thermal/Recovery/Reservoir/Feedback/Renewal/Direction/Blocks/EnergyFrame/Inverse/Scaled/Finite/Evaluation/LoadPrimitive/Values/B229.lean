import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B152
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B153

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3665_pa : Scalar.QComplex := ((999998204461682978888613510219 : Int)/10^30,(-1895012773066285926023695731 : Int)/10^30)
theorem v3665_pa_checked : Scalar.distance (sourceCoefficient 50 91 1 0) v3665_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3665_pb : Scalar.QComplex := ((-817655339061575272978288 : Int)/10^30,(-431476706939052931625868002 : Int)/10^30)
theorem v3665_pb_checked : Scalar.distance (sourceCoefficient 50 91 1 1) v3665_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3665_pg : Scalar.QComplex := ((-93086258514525877020930 : Int)/10^30,(176399965614874234553 : Int)/10^30)
theorem v3665_pg_checked : Scalar.distance (sourceCoefficient 50 91 1 2) v3665_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3665_mb : Scalar.QComplex := ((-1189999999710032469443274 : Int)/10^30,(-431475840680823697841100498 : Int)/10^30)
theorem v3665_mb_checked : Scalar.distance (sourceCoefficient 50 91 3 1) v3665_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3665_mg : Scalar.QComplex := ((-93086071629032013776004 : Int)/10^30,(256729148581688536241 : Int)/10^30)
theorem v3665_mg_checked : Scalar.distance (sourceCoefficient 50 91 3 2) v3665_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3665_upper : Scalar.QComplex := ((999993444461693377430599570083 : Int)/10^30,(-3620916132439779280251179072 : Int)/10^30)
theorem v3665_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 91 5) 1) 14) v3665_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3665 : Material (50 : Basis) (91 : Basis) where
  plus := ![v3665_pa,v3665_pb,v3665_pg]
  minus := ![(Primitive.Addresses.material3665 1).one,v3665_mb,v3665_mg]
  upper := v3665_upper
  lower := (Primitive.Addresses.material3665 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3665_pa_checked.trans (by decide +kernel)
    · exact v3665_pb_checked.trans (by decide +kernel)
    · exact v3665_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 91 Primitive.Addresses.material3665
    · exact v3665_mb_checked.trans (by decide +kernel)
    · exact v3665_mg_checked.trans (by decide +kernel)
  upper_error := v3665_upper_checked
  lower_error := reuse_lower_error 50 91 Primitive.Addresses.material3665

def v3666_pa : Scalar.QComplex := ((999998143393861126218971234006 : Int)/10^30,(-1926968819353651906340844324 : Int)/10^30)
theorem v3666_pa_checked : Scalar.distance (sourceCoefficient 50 92 1 0) v3666_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3666_pb : Scalar.QComplex := ((-831443646746866969305641 : Int)/10^30,(-431476677117366340770477839 : Int)/10^30)
theorem v3666_pb_checked : Scalar.distance (sourceCoefficient 50 92 1 1) v3666_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3666_pg : Scalar.QComplex := ((-93086252455386114160958 : Int)/10^30,(179374639020067324154 : Int)/10^30)
theorem v3666_pg_checked : Scalar.distance (sourceCoefficient 50 92 1 2) v3666_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3666_mb : Scalar.QComplex := ((-1203788276526534648741867 : Int)/10^30,(-431475798960459680881268203 : Int)/10^30)
theorem v3666_mb_checked : Scalar.distance (sourceCoefficient 50 92 3 1) v3666_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3666_mg : Scalar.QComplex := ((-93086063002885332645854 : Int)/10^30,(259703815650510045975 : Int)/10^30)
theorem v3666_mg_checked : Scalar.distance (sourceCoefficient 50 92 3 2) v3666_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3666_upper : Scalar.QComplex := ((999993328240725615987605797153 : Int)/10^30,(-3652872025734847648239485206 : Int)/10^30)
theorem v3666_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 92 5) 1) 14) v3666_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3666 : Material (50 : Basis) (92 : Basis) where
  plus := ![v3666_pa,v3666_pb,v3666_pg]
  minus := ![(Primitive.Addresses.material3666 1).one,v3666_mb,v3666_mg]
  upper := v3666_upper
  lower := (Primitive.Addresses.material3666 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3666_pa_checked.trans (by decide +kernel)
    · exact v3666_pb_checked.trans (by decide +kernel)
    · exact v3666_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 92 Primitive.Addresses.material3666
    · exact v3666_mb_checked.trans (by decide +kernel)
    · exact v3666_mg_checked.trans (by decide +kernel)
  upper_error := v3666_upper_checked
  lower_error := reuse_lower_error 50 92 Primitive.Addresses.material3666

def v3667_pa : Scalar.QComplex := ((999998069593215266838720485019 : Int)/10^30,(-1964894359245801289449340576 : Int)/10^30)
theorem v3667_pa_checked : Scalar.distance (sourceCoefficient 50 93 1 0) v3667_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3667_pb : Scalar.QComplex := ((-847807654587241682377908 : Int)/10^30,(-431476640962525967403543411 : Int)/10^30)
theorem v3667_pb_checked : Scalar.distance (sourceCoefficient 50 93 1 1) v3667_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3667_pg : Scalar.QComplex := ((-93086245120466379591334 : Int)/10^30,(182904991041612052075 : Int)/10^30)
theorem v3667_pg_checked : Scalar.distance (sourceCoefficient 50 93 1 2) v3667_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3667_mb : Scalar.QComplex := ((-1220152247073842482086117 : Int)/10^30,(-431475748684231010924509277 : Int)/10^30)
theorem v3667_mb_checked : Scalar.distance (sourceCoefficient 50 93 3 1) v3667_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3667_mg : Scalar.QComplex := ((-93086052621433535761620 : Int)/10^30,(263234160027837992805 : Int)/10^30)
theorem v3667_mg_checked : Scalar.distance (sourceCoefficient 50 93 3 2) v3667_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3667_upper : Scalar.QComplex := ((999993188984148398252989089805 : Int)/10^30,(-3690797381768140797859649453 : Int)/10^30)
theorem v3667_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 93 5) 1) 14) v3667_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3667 : Material (50 : Basis) (93 : Basis) where
  plus := ![v3667_pa,v3667_pb,v3667_pg]
  minus := ![(Primitive.Addresses.material3667 1).one,v3667_mb,v3667_mg]
  upper := v3667_upper
  lower := (Primitive.Addresses.material3667 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3667_pa_checked.trans (by decide +kernel)
    · exact v3667_pb_checked.trans (by decide +kernel)
    · exact v3667_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 93 Primitive.Addresses.material3667
    · exact v3667_mb_checked.trans (by decide +kernel)
    · exact v3667_mg_checked.trans (by decide +kernel)
  upper_error := v3667_upper_checked
  lower_error := reuse_lower_error 50 93 Primitive.Addresses.material3667

def v3668_pa : Scalar.QComplex := ((999997980565328928762154255003 : Int)/10^30,(-2009692828276521707031473110 : Int)/10^30)
theorem v3668_pa_checked : Scalar.distance (sourceCoefficient 50 94 1 0) v3668_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3668_pb : Scalar.QComplex := ((-867137174068030943561830 : Int)/10^30,(-431476597189630021730882168 : Int)/10^30)
theorem v3668_pb_checked : Scalar.distance (sourceCoefficient 50 94 1 1) v3668_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3668_pg : Scalar.QComplex := ((-93086236255066944207491 : Int)/10^30,(187075119199043786718 : Int)/10^30)
theorem v3668_pg_checked : Scalar.distance (sourceCoefficient 50 94 1 2) v3668_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3668_mb : Scalar.QComplex := ((-1239481721583330494824872 : Int)/10^30,(-431475688230846621220761849 : Int)/10^30)
theorem v3668_mb_checked : Scalar.distance (sourceCoefficient 50 94 3 1) v3668_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3668_mg : Scalar.QComplex := ((-93086040157404617107737 : Int)/10^30,(267404278982100000196 : Int)/10^30)
theorem v3668_mg_checked : Scalar.distance (sourceCoefficient 50 94 3 2) v3668_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3668_upper : Scalar.QComplex := ((999993022638301195095306832307 : Int)/10^30,(-3735595630422748719257270412 : Int)/10^30)
theorem v3668_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 94 5) 1) 14) v3668_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3668 : Material (50 : Basis) (94 : Basis) where
  plus := ![v3668_pa,v3668_pb,v3668_pg]
  minus := ![(Primitive.Addresses.material3668 1).one,v3668_mb,v3668_mg]
  upper := v3668_upper
  lower := (Primitive.Addresses.material3668 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3668_pa_checked.trans (by decide +kernel)
    · exact v3668_pb_checked.trans (by decide +kernel)
    · exact v3668_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 94 Primitive.Addresses.material3668
    · exact v3668_mb_checked.trans (by decide +kernel)
    · exact v3668_mg_checked.trans (by decide +kernel)
  upper_error := v3668_upper_checked
  lower_error := reuse_lower_error 50 94 Primitive.Addresses.material3668

def v3669_pa : Scalar.QComplex := ((999997890607637701156209779824 : Int)/10^30,(-2053966960557435416447243096 : Int)/10^30)
theorem v3669_pa_checked : Scalar.distance (sourceCoefficient 50 95 1 0) v3669_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3669_pb : Scalar.QComplex := ((-886240453124322286993546 : Int)/10^30,(-431476552794675428657966787 : Int)/10^30)
theorem v3669_pb_checked : Scalar.distance (sourceCoefficient 50 95 1 1) v3669_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3669_pg : Scalar.QComplex := ((-93086227279290314238480 : Int)/10^30,(191196438622909887469 : Int)/10^30)
theorem v3669_pg_checked : Scalar.distance (sourceCoefficient 50 95 1 2) v3669_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3669_mb : Scalar.QComplex := ((-1258584955215751643325224 : Int)/10^30,(-431475627350639112588859494 : Int)/10^30)
theorem v3669_mb_checked : Scalar.distance (sourceCoefficient 50 95 3 1) v3669_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3669_mg : Scalar.QComplex := ((-93086027625118283770545 : Int)/10^30,(271525589125719548149 : Int)/10^30)
theorem v3669_mg_checked : Scalar.distance (sourceCoefficient 50 95 3 2) v3669_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3669_upper : Scalar.QComplex := ((999992856267608149951419152670 : Int)/10^30,(-3779869541503729040317277125 : Int)/10^30)
theorem v3669_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 95 5) 1) 14) v3669_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3669 : Material (50 : Basis) (95 : Basis) where
  plus := ![v3669_pa,v3669_pb,v3669_pg]
  minus := ![(Primitive.Addresses.material3669 1).one,v3669_mb,v3669_mg]
  upper := v3669_upper
  lower := (Primitive.Addresses.material3669 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3669_pa_checked.trans (by decide +kernel)
    · exact v3669_pb_checked.trans (by decide +kernel)
    · exact v3669_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 95 Primitive.Addresses.material3669
    · exact v3669_mb_checked.trans (by decide +kernel)
    · exact v3669_mg_checked.trans (by decide +kernel)
  upper_error := v3669_upper_checked
  lower_error := reuse_lower_error 50 95 Primitive.Addresses.material3669

def v3670_pa : Scalar.QComplex := ((999997846705805315220115636551 : Int)/10^30,(-2075231011886067325582927010 : Int)/10^30)
theorem v3670_pa_checked : Scalar.distance (sourceCoefficient 50 96 1 0) v3670_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3670_pb : Scalar.QComplex := ((-895415406273851889383877 : Int)/10^30,(-431476531071720030617089487 : Int)/10^30)
theorem v3670_pb_checked : Scalar.distance (sourceCoefficient 50 96 1 1) v3670_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3670_pg : Scalar.QComplex := ((-93086222892716042345317 : Int)/10^30,(193175832490701773287 : Int)/10^30)
theorem v3670_pg_checked : Scalar.distance (sourceCoefficient 50 96 1 2) v3670_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3670_mb : Scalar.QComplex := ((-1267759886203094729155329 : Int)/10^30,(-431475597710120459503256592 : Int)/10^30)
theorem v3670_mb_checked : Scalar.distance (sourceCoefficient 50 96 3 1) v3670_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3670_mg : Scalar.QComplex := ((-93086021530417885885516 : Int)/10^30,(273504978471076601547 : Int)/10^30)
theorem v3670_mg_checked : Scalar.distance (sourceCoefficient 50 96 3 2) v3670_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3670_upper : Scalar.QComplex := ((999992775666017617086463522150 : Int)/10^30,(-3801133485391474391386123180 : Int)/10^30)
theorem v3670_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 96 5) 1) 14) v3670_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3670 : Material (50 : Basis) (96 : Basis) where
  plus := ![v3670_pa,v3670_pb,v3670_pg]
  minus := ![(Primitive.Addresses.material3670 1).one,v3670_mb,v3670_mg]
  upper := v3670_upper
  lower := (Primitive.Addresses.material3670 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3670_pa_checked.trans (by decide +kernel)
    · exact v3670_pb_checked.trans (by decide +kernel)
    · exact v3670_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 96 Primitive.Addresses.material3670
    · exact v3670_mb_checked.trans (by decide +kernel)
    · exact v3670_mg_checked.trans (by decide +kernel)
  upper_error := v3670_upper_checked
  lower_error := reuse_lower_error 50 96 Primitive.Addresses.material3670

def v3671_pa : Scalar.QComplex := ((999997692200941059448172121969 : Int)/10^30,(-2148393072029559307957631248 : Int)/10^30)
theorem v3671_pa_checked : Scalar.distance (sourceCoefficient 50 97 1 0) v3671_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3671_pb : Scalar.QComplex := ((-926983164546347426471614 : Int)/10^30,(-431476454343508740976757890 : Int)/10^30)
theorem v3671_pb_checked : Scalar.distance (sourceCoefficient 50 97 1 1) v3671_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3671_pg : Scalar.QComplex := ((-93086207424937926930244 : Int)/10^30,(199986224661264240458 : Int)/10^30)
theorem v3671_pg_checked : Scalar.distance (sourceCoefficient 50 97 1 2) v3671_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3671_mb : Scalar.QComplex := ((-1299327566508480510963098 : Int)/10^30,(-431475493740384109173408348 : Int)/10^30)
theorem v3671_mb_checked : Scalar.distance (sourceCoefficient 50 97 3 1) v3671_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3671_mg : Scalar.QComplex := ((-93086000185583815312797 : Int)/10^30,(280315354757822942582 : Int)/10^30)
theorem v3671_mg_checked : Scalar.distance (sourceCoefficient 50 97 3 2) v3671_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3671_upper : Scalar.QComplex := ((999992494890304880742427526981 : Int)/10^30,(-3874295169907292875656411435 : Int)/10^30)
theorem v3671_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 97 5) 1) 14) v3671_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3671 : Material (50 : Basis) (97 : Basis) where
  plus := ![v3671_pa,v3671_pb,v3671_pg]
  minus := ![(Primitive.Addresses.material3671 1).one,v3671_mb,v3671_mg]
  upper := v3671_upper
  lower := (Primitive.Addresses.material3671 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3671_pa_checked.trans (by decide +kernel)
    · exact v3671_pb_checked.trans (by decide +kernel)
    · exact v3671_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 97 Primitive.Addresses.material3671
    · exact v3671_mb_checked.trans (by decide +kernel)
    · exact v3671_mg_checked.trans (by decide +kernel)
  upper_error := v3671_upper_checked
  lower_error := reuse_lower_error 50 97 Primitive.Addresses.material3671

def v3672_pa : Scalar.QComplex := ((999999277246360831828681665433 : Int)/10^30,(-1202292292233265423687643754 : Int)/10^30)
theorem v3672_pa_checked : Scalar.distance (sourceCoefficient 51 52 1 0) v3672_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3672_pb : Scalar.QComplex := ((-518762097720413289429306 : Int)/10^30,(-431477209106627613222917177 : Int)/10^30)
theorem v3672_pb_checked : Scalar.distance (sourceCoefficient 51 52 1 1) v3672_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3672_pg : Scalar.QComplex := ((-93086362613881314801534 : Int)/10^30,(111917097171189572418 : Int)/10^30)
theorem v3672_pg_checked : Scalar.distance (sourceCoefficient 51 52 1 2) v3672_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3672_mb : Scalar.QComplex := ((-891107303008484495389850 : Int)/10^30,(-431476600779617025052696614 : Int)/10^30)
theorem v3672_mb_checked : Scalar.distance (sourceCoefficient 51 52 3 1) v3672_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3672_mg : Scalar.QComplex := ((-93086231374159956923156 : Int)/10^30,(192246393980978090244 : Int)/10^30)
theorem v3672_mg_checked : Scalar.distance (sourceCoefficient 51 52 3 2) v3672_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3672_upper : Scalar.QComplex := ((999995712817480250286805795721 : Int)/10^30,(-2928198534861574023342210688 : Int)/10^30)
theorem v3672_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 52 5) 1) 14) v3672_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3672 : Material (51 : Basis) (52 : Basis) where
  plus := ![v3672_pa,v3672_pb,v3672_pg]
  minus := ![(Primitive.Addresses.material3672 1).one,v3672_mb,v3672_mg]
  upper := v3672_upper
  lower := (Primitive.Addresses.material3672 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3672_pa_checked.trans (by decide +kernel)
    · exact v3672_pb_checked.trans (by decide +kernel)
    · exact v3672_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 52 Primitive.Addresses.material3672
    · exact v3672_mb_checked.trans (by decide +kernel)
    · exact v3672_mg_checked.trans (by decide +kernel)
  upper_error := v3672_upper_checked
  lower_error := reuse_lower_error 51 52 Primitive.Addresses.material3672

def v3673_pa : Scalar.QComplex := ((999999272787790380060265839010 : Int)/10^30,(-1205994979426648213609512561 : Int)/10^30)
theorem v3673_pa_checked : Scalar.distance (sourceCoefficient 51 53 1 0) v3673_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3673_pb : Scalar.QComplex := ((-520359723994774963034608 : Int)/10^30,(-431477207168987143785167815 : Int)/10^30)
theorem v3673_pb_checked : Scalar.distance (sourceCoefficient 51 53 1 1) v3673_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3673_pg : Scalar.QComplex := ((-93086362197353025601810 : Int)/10^30,(112261767101225995631 : Int)/10^30)
theorem v3673_pg_checked : Scalar.distance (sourceCoefficient 51 53 1 2) v3673_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3673_mb : Scalar.QComplex := ((-892704927015880434884964 : Int)/10^30,(-431476597463297756729248008 : Int)/10^30)
theorem v3673_mb_checked : Scalar.distance (sourceCoefficient 51 53 3 1) v3673_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3673_mg : Scalar.QComplex := ((-93086230660197196551912 : Int)/10^30,(192591063423232992468 : Int)/10^30)
theorem v3673_mg_checked : Scalar.distance (sourceCoefficient 51 53 3 2) v3673_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3673_upper : Scalar.QComplex := ((999995701968414248414878585734 : Int)/10^30,(-2931901208845151065511079873 : Int)/10^30)
theorem v3673_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 53 5) 1) 14) v3673_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3673 : Material (51 : Basis) (53 : Basis) where
  plus := ![v3673_pa,v3673_pb,v3673_pg]
  minus := ![(Primitive.Addresses.material3673 1).one,v3673_mb,v3673_mg]
  upper := v3673_upper
  lower := (Primitive.Addresses.material3673 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3673_pa_checked.trans (by decide +kernel)
    · exact v3673_pb_checked.trans (by decide +kernel)
    · exact v3673_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 53 Primitive.Addresses.material3673
    · exact v3673_mb_checked.trans (by decide +kernel)
    · exact v3673_mg_checked.trans (by decide +kernel)
  upper_error := v3673_upper_checked
  lower_error := reuse_lower_error 51 53 Primitive.Addresses.material3673

def v3674_pa : Scalar.QComplex := ((999999270515769163741665357743 : Int)/10^30,(-1207877448057241289976382635 : Int)/10^30)
theorem v3674_pa_checked : Scalar.distance (sourceCoefficient 51 54 1 0) v3674_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3674_pb : Scalar.QComplex := ((-521171966883330228925219 : Int)/10^30,(-431477206180854633972741132 : Int)/10^30)
theorem v3674_pb_checked : Scalar.distance (sourceCoefficient 51 54 1 1) v3674_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3674_pg : Scalar.QComplex := ((-93086361985016607371473 : Int)/10^30,(112436999384412470864 : Int)/10^30)
theorem v3674_pg_checked : Scalar.distance (sourceCoefficient 51 54 1 2) v3674_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3674_mb : Scalar.QComplex := ((-893517168749286699900670 : Int)/10^30,(-431476595774236584082230716 : Int)/10^30)
theorem v3674_mb_checked : Scalar.distance (sourceCoefficient 51 54 3 1) v3674_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3674_mg : Scalar.QComplex := ((-93086230296643289163262 : Int)/10^30,(192766295457935714504 : Int)/10^30)
theorem v3674_mg_checked : Scalar.distance (sourceCoefficient 51 54 3 2) v3674_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3674_upper : Scalar.QComplex := ((999995696447426335821476423345 : Int)/10^30,(-2933783670750725743697217388 : Int)/10^30)
theorem v3674_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 54 5) 1) 14) v3674_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3674 : Material (51 : Basis) (54 : Basis) where
  plus := ![v3674_pa,v3674_pb,v3674_pg]
  minus := ![(Primitive.Addresses.material3674 1).one,v3674_mb,v3674_mg]
  upper := v3674_upper
  lower := (Primitive.Addresses.material3674 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3674_pa_checked.trans (by decide +kernel)
    · exact v3674_pb_checked.trans (by decide +kernel)
    · exact v3674_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 54 Primitive.Addresses.material3674
    · exact v3674_mb_checked.trans (by decide +kernel)
    · exact v3674_mg_checked.trans (by decide +kernel)
  upper_error := v3674_upper_checked
  lower_error := reuse_lower_error 51 54 Primitive.Addresses.material3674

def v3675_pa : Scalar.QComplex := ((999999251864872663766256656754 : Int)/10^30,(-1223221032751766712476973514 : Int)/10^30)
theorem v3675_pa_checked : Scalar.distance (sourceCoefficient 51 55 1 0) v3675_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3675_pb : Scalar.QComplex := ((-527792378668527603558459 : Int)/10^30,(-431477198050776310228169827 : Int)/10^30)
theorem v3675_pb_checked : Scalar.distance (sourceCoefficient 51 55 1 1) v3675_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3675_pg : Scalar.QComplex := ((-93086360239957371688270 : Int)/10^30,(113865278894438575713 : Int)/10^30)
theorem v3675_pg_checked : Scalar.distance (sourceCoefficient 51 55 1 2) v3675_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3675_mb : Scalar.QComplex := ((-900137571053510770882640 : Int)/10^30,(-431476581931044089190178006 : Int)/10^30)
theorem v3675_mb_checked : Scalar.distance (sourceCoefficient 51 55 3 1) v3675_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3675_mg : Scalar.QComplex := ((-93086227319043813414027 : Int)/10^30,(194194572930240556328 : Int)/10^30)
theorem v3675_mg_checked : Scalar.distance (sourceCoefficient 51 55 3 2) v3675_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3675_upper : Scalar.QComplex := ((999995651314922390544736331352 : Int)/10^30,(-2949127200403028784926759762 : Int)/10^30)
theorem v3675_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 55 5) 1) 14) v3675_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3675 : Material (51 : Basis) (55 : Basis) where
  plus := ![v3675_pa,v3675_pb,v3675_pg]
  minus := ![(Primitive.Addresses.material3675 1).one,v3675_mb,v3675_mg]
  upper := v3675_upper
  lower := (Primitive.Addresses.material3675 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3675_pa_checked.trans (by decide +kernel)
    · exact v3675_pb_checked.trans (by decide +kernel)
    · exact v3675_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 55 Primitive.Addresses.material3675
    · exact v3675_mb_checked.trans (by decide +kernel)
    · exact v3675_mg_checked.trans (by decide +kernel)
  upper_error := v3675_upper_checked
  lower_error := reuse_lower_error 51 55 Primitive.Addresses.material3675

def v3676_pa : Scalar.QComplex := ((999999247403927276419866058002 : Int)/10^30,(-1226862493943926704195317284 : Int)/10^30)
theorem v3676_pa_checked : Scalar.distance (sourceCoefficient 51 56 1 0) v3676_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3676_pb : Scalar.QComplex := ((-529363587285847404207081 : Int)/10^30,(-431477196101395303117137027 : Int)/10^30)
theorem v3676_pb_checked : Scalar.distance (sourceCoefficient 51 56 1 1) v3676_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3676_pg : Scalar.QComplex := ((-93086359822052100780486 : Int)/10^30,(114204249513114249485 : Int)/10^30)
theorem v3676_pg_checked : Scalar.distance (sourceCoefficient 51 56 1 2) v3676_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3676_mb : Scalar.QComplex := ((-901708777403569783246479 : Int)/10^30,(-431476578625781535785015617 : Int)/10^30)
theorem v3676_mb_checked : Scalar.distance (sourceCoefficient 51 56 3 1) v3676_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3676_mg : Scalar.QComplex := ((-93086226608622320864308 : Int)/10^30,(194533543062068550006 : Int)/10^30)
theorem v3676_mg_checked : Scalar.distance (sourceCoefficient 51 56 3 2) v3676_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3676_upper : Scalar.QComplex := ((999995640569151980363129111048 : Int)/10^30,(-2952768648472473042247028095 : Int)/10^30)
theorem v3676_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 56 5) 1) 14) v3676_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3676 : Material (51 : Basis) (56 : Basis) where
  plus := ![v3676_pa,v3676_pb,v3676_pg]
  minus := ![(Primitive.Addresses.material3676 1).one,v3676_mb,v3676_mg]
  upper := v3676_upper
  lower := (Primitive.Addresses.material3676 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3676_pa_checked.trans (by decide +kernel)
    · exact v3676_pb_checked.trans (by decide +kernel)
    · exact v3676_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 56 Primitive.Addresses.material3676
    · exact v3676_mb_checked.trans (by decide +kernel)
    · exact v3676_mg_checked.trans (by decide +kernel)
  upper_error := v3676_upper_checked
  lower_error := reuse_lower_error 51 56 Primitive.Addresses.material3676

def v3677_pa : Scalar.QComplex := ((999999232884758158820938504503 : Int)/10^30,(-1238640341348756434059466798 : Int)/10^30)
theorem v3677_pa_checked : Scalar.distance (sourceCoefficient 51 57 1 0) v3677_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3677_pb : Scalar.QComplex := ((-534445463570130649140012 : Int)/10^30,(-431477189744128611055001367 : Int)/10^30)
theorem v3677_pb_checked : Scalar.distance (sourceCoefficient 51 57 1 1) v3677_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3677_pg : Scalar.QComplex := ((-93086358460528841683613 : Int)/10^30,(115300607267315374241 : Int)/10^30)
theorem v3677_pg_checked : Scalar.distance (sourceCoefficient 51 57 1 2) v3677_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3677_mb : Scalar.QComplex := ((-906790646309603399734489 : Int)/10^30,(-431476567883086856698818888 : Int)/10^30)
theorem v3677_mb_checked : Scalar.distance (sourceCoefficient 51 57 3 1) v3677_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3677_mg : Scalar.QComplex := ((-93086224300992204969445 : Int)/10^30,(195629899233112324979 : Int)/10^30)
theorem v3677_mg_checked : Scalar.distance (sourceCoefficient 51 57 3 2) v3677_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3677_upper : Scalar.QComplex := ((999995605722508344595021356245 : Int)/10^30,(-2964546453276813857518108490 : Int)/10^30)
theorem v3677_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 57 5) 1) 14) v3677_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3677 : Material (51 : Basis) (57 : Basis) where
  plus := ![v3677_pa,v3677_pb,v3677_pg]
  minus := ![(Primitive.Addresses.material3677 1).one,v3677_mb,v3677_mg]
  upper := v3677_upper
  lower := (Primitive.Addresses.material3677 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3677_pa_checked.trans (by decide +kernel)
    · exact v3677_pb_checked.trans (by decide +kernel)
    · exact v3677_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 57 Primitive.Addresses.material3677
    · exact v3677_mb_checked.trans (by decide +kernel)
    · exact v3677_mg_checked.trans (by decide +kernel)
  upper_error := v3677_upper_checked
  lower_error := reuse_lower_error 51 57 Primitive.Addresses.material3677

def v3678_pa : Scalar.QComplex := ((999999224948745215205634610878 : Int)/10^30,(-1245030886711306125295616853 : Int)/10^30)
theorem v3678_pa_checked : Scalar.distance (sourceCoefficient 51 58 1 0) v3678_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3678_pb : Scalar.QComplex := ((-537202840166390194178090 : Int)/10^30,(-431477186261339450617476726 : Int)/10^30)
theorem v3678_pb_checked : Scalar.distance (sourceCoefficient 51 58 1 1) v3678_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3678_pg : Scalar.QComplex := ((-93086357715474959708873 : Int)/10^30,(115895480312161061248 : Int)/10^30)
theorem v3678_pg_checked : Scalar.distance (sourceCoefficient 51 58 1 2) v3678_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3678_mb : Scalar.QComplex := ((-909548018873675433192579 : Int)/10^30,(-431476562020807178122716576 : Int)/10^30)
theorem v3678_mb_checked : Scalar.distance (sourceCoefficient 51 58 3 1) v3678_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3678_mg : Scalar.QComplex := ((-93086223042589954797859 : Int)/10^30,(196224771413511646186 : Int)/10^30)
theorem v3678_mg_checked : Scalar.distance (sourceCoefficient 51 58 3 2) v3678_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3678_upper : Scalar.QComplex := ((999995586757005670724565603084 : Int)/10^30,(-2970936975424558526217900965 : Int)/10^30)
theorem v3678_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 58 5) 1) 14) v3678_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3678 : Material (51 : Basis) (58 : Basis) where
  plus := ![v3678_pa,v3678_pb,v3678_pg]
  minus := ![(Primitive.Addresses.material3678 1).one,v3678_mb,v3678_mg]
  upper := v3678_upper
  lower := (Primitive.Addresses.material3678 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3678_pa_checked.trans (by decide +kernel)
    · exact v3678_pb_checked.trans (by decide +kernel)
    · exact v3678_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 58 Primitive.Addresses.material3678
    · exact v3678_mb_checked.trans (by decide +kernel)
    · exact v3678_mg_checked.trans (by decide +kernel)
  upper_error := v3678_upper_checked
  lower_error := reuse_lower_error 51 58 Primitive.Addresses.material3678

def v3679_pa : Scalar.QComplex := ((999999202924342742976976533448 : Int)/10^30,(-1262596799926422534578121592 : Int)/10^30)
theorem v3679_pa_checked : Scalar.distance (sourceCoefficient 51 59 1 0) v3679_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3679_pb : Scalar.QComplex := ((-544782136607396349338513 : Int)/10^30,(-431477176567027374179908859 : Int)/10^30)
theorem v3679_pb_checked : Scalar.distance (sourceCoefficient 51 59 1 1) v3679_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3679_pg : Scalar.QComplex := ((-93086355644668977211853 : Int)/10^30,(117530628434574836893 : Int)/10^30)
theorem v3679_pg_checked : Scalar.distance (sourceCoefficient 51 59 1 2) v3679_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3679_mb : Scalar.QComplex := ((-917127304126808426049365 : Int)/10^30,(-431476545785907241572141949 : Int)/10^30)
theorem v3679_mb_checked : Scalar.distance (sourceCoefficient 51 59 3 1) v3679_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3679_mg : Scalar.QComplex := ((-93086219560725558051086 : Int)/10^30,(197859917140072748639 : Int)/10^30)
theorem v3679_mg_checked : Scalar.distance (sourceCoefficient 51 59 3 2) v3679_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3679_upper : Scalar.QComplex := ((999995534415463359163910981394 : Int)/10^30,(-2988502824465190009817112233 : Int)/10^30)
theorem v3679_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 59 5) 1) 14) v3679_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3679 : Material (51 : Basis) (59 : Basis) where
  plus := ![v3679_pa,v3679_pb,v3679_pg]
  minus := ![(Primitive.Addresses.material3679 1).one,v3679_mb,v3679_mg]
  upper := v3679_upper
  lower := (Primitive.Addresses.material3679 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3679_pa_checked.trans (by decide +kernel)
    · exact v3679_pb_checked.trans (by decide +kernel)
    · exact v3679_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 59 Primitive.Addresses.material3679
    · exact v3679_mb_checked.trans (by decide +kernel)
    · exact v3679_mg_checked.trans (by decide +kernel)
  upper_error := v3679_upper_checked
  lower_error := reuse_lower_error 51 59 Primitive.Addresses.material3679

def v3680_pa : Scalar.QComplex := ((999999177133856050275490805853 : Int)/10^30,(-1282860713713986238578412395 : Int)/10^30)
theorem v3680_pa_checked : Scalar.distance (sourceCoefficient 51 60 1 0) v3680_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3680_pb : Scalar.QComplex := ((-553525559530029796451596 : Int)/10^30,(-431477165163228667814792096 : Int)/10^30)
theorem v3680_pb_checked : Scalar.distance (sourceCoefficient 51 60 1 1) v3680_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3680_pg : Scalar.QComplex := ((-93086353214176055508274 : Int)/10^30,(119416923785513709195 : Int)/10^30)
theorem v3680_pg_checked : Scalar.distance (sourceCoefficient 51 60 1 2) v3680_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3680_mb : Scalar.QComplex := ((-925870713952901249332712 : Int)/10^30,(-431476526836932588280093075 : Int)/10^30)
theorem v3680_mb_checked : Scalar.distance (sourceCoefficient 51 60 3 1) v3680_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3680_mg : Scalar.QComplex := ((-93086215502445609059760 : Int)/10^30,(199746209691251727738 : Int)/10^30)
theorem v3680_mg_checked : Scalar.distance (sourceCoefficient 51 60 3 2) v3680_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3680_upper : Scalar.QComplex := ((999995473651338208926415847840 : Int)/10^30,(-3008766663559994156839687278 : Int)/10^30)
theorem v3680_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 51 60 5) 1) 14) v3680_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3680 : Material (51 : Basis) (60 : Basis) where
  plus := ![v3680_pa,v3680_pb,v3680_pg]
  minus := ![(Primitive.Addresses.material3680 1).one,v3680_mb,v3680_mg]
  upper := v3680_upper
  lower := (Primitive.Addresses.material3680 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3680_pa_checked.trans (by decide +kernel)
    · exact v3680_pb_checked.trans (by decide +kernel)
    · exact v3680_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 51 60 Primitive.Addresses.material3680
    · exact v3680_mb_checked.trans (by decide +kernel)
    · exact v3680_mg_checked.trans (by decide +kernel)
  upper_error := v3680_upper_checked
  lower_error := reuse_lower_error 51 60 Primitive.Addresses.material3680

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
