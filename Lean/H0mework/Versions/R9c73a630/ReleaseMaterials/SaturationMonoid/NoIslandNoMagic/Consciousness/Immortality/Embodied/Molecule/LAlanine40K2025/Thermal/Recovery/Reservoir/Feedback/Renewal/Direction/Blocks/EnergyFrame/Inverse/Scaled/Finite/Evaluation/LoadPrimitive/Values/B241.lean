import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B160
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B161

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3857_pa : Scalar.QComplex := ((999999065455196706536708444409 : Int)/10^30,(-1367146200379804742224691289 : Int)/10^30)
theorem v3857_pa_checked : Scalar.distance (sourceCoefficient 55 63 1 0) v3857_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3857_pb : Scalar.QComplex := ((-589892852425491422186521 : Int)/10^30,(-431477117063496671214472093 : Int)/10^30)
theorem v3857_pb_checked : Scalar.distance (sourceCoefficient 55 63 1 1) v3857_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3857_pg : Scalar.QComplex := ((-93086342827803686268302 : Int)/10^30,(127262758837033622409 : Int)/10^30)
theorem v3857_pg_checked : Scalar.distance (sourceCoefficient 55 63 1 2) v3857_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3857_mb : Scalar.QComplex := ((-962237951799255281139200 : Int)/10^30,(-431476447353882654694365070 : Int)/10^30)
theorem v3857_mb_checked : Scalar.distance (sourceCoefficient 55 63 3 1) v3857_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3857_mg : Scalar.QComplex := ((-93086198345474820972475 : Int)/10^30,(207592032858437109088 : Int)/10^30)
theorem v3857_mg_checked : Scalar.distance (sourceCoefficient 55 63 3 2) v3857_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3857_upper : Scalar.QComplex := ((999995216503741531849843879765 : Int)/10^30,(-3093051831945246522051472071 : Int)/10^30)
theorem v3857_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 63 5) 1) 14) v3857_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3857 : Material (55 : Basis) (63 : Basis) where
  plus := ![v3857_pa,v3857_pb,v3857_pg]
  minus := ![(Primitive.Addresses.material3857 1).one,v3857_mb,v3857_mg]
  upper := v3857_upper
  lower := (Primitive.Addresses.material3857 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3857_pa_checked.trans (by decide +kernel)
    · exact v3857_pb_checked.trans (by decide +kernel)
    · exact v3857_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 63 Primitive.Addresses.material3857
    · exact v3857_mb_checked.trans (by decide +kernel)
    · exact v3857_mg_checked.trans (by decide +kernel)
  upper_error := v3857_upper_checked
  lower_error := reuse_lower_error 55 63 Primitive.Addresses.material3857

def v3858_pa : Scalar.QComplex := ((999999016379366176380805348452 : Int)/10^30,(-1402583437852339359258473889 : Int)/10^30)
theorem v3858_pa_checked : Scalar.distance (sourceCoefficient 55 64 1 0) v3858_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3858_pb : Scalar.QComplex := ((-605183222943363389133747 : Int)/10^30,(-431477095294469206842639542 : Int)/10^30)
theorem v3858_pb_checked : Scalar.distance (sourceCoefficient 55 64 1 1) v3858_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3858_pg : Scalar.QComplex := ((-93086338195445147170485 : Int)/10^30,(130561484666223282460 : Int)/10^30)
theorem v3858_pg_checked : Scalar.distance (sourceCoefficient 55 64 1 2) v3858_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3858_mb : Scalar.QComplex := ((-977528297838133238676824 : Int)/10^30,(-431476412389962191726977921 : Int)/10^30)
theorem v3858_mb_checked : Scalar.distance (sourceCoefficient 55 64 3 1) v3858_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3858_mg : Scalar.QComplex := ((-93086190866466185218978 : Int)/10^30,(210890753461843598155 : Int)/10^30)
theorem v3858_mg_checked : Scalar.distance (sourceCoefficient 55 64 3 2) v3858_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3858_upper : Scalar.QComplex := ((999995106266527057854462494072 : Int)/10^30,(-3128488931937747303594246825 : Int)/10^30)
theorem v3858_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 64 5) 1) 14) v3858_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3858 : Material (55 : Basis) (64 : Basis) where
  plus := ![v3858_pa,v3858_pb,v3858_pg]
  minus := ![(Primitive.Addresses.material3858 1).one,v3858_mb,v3858_mg]
  upper := v3858_upper
  lower := (Primitive.Addresses.material3858 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3858_pa_checked.trans (by decide +kernel)
    · exact v3858_pb_checked.trans (by decide +kernel)
    · exact v3858_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 64 Primitive.Addresses.material3858
    · exact v3858_mb_checked.trans (by decide +kernel)
    · exact v3858_mg_checked.trans (by decide +kernel)
  upper_error := v3858_upper_checked
  lower_error := reuse_lower_error 55 64 Primitive.Addresses.material3858

def v3859_pa : Scalar.QComplex := ((999998965286384037179627011385 : Int)/10^30,(-1438550020434942570482579483 : Int)/10^30)
theorem v3859_pa_checked : Scalar.distance (sourceCoefficient 55 65 1 0) v3859_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3859_pb : Scalar.QComplex := ((-620701993655549200621156 : Int)/10^30,(-431477072461531204146475217 : Int)/10^30)
theorem v3859_pb_checked : Scalar.distance (sourceCoefficient 55 65 1 1) v3859_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3859_pg : Scalar.QComplex := ((-93086333354438511554554 : Int)/10^30,(133909485307209150934 : Int)/10^30)
theorem v3859_pg_checked : Scalar.distance (sourceCoefficient 55 65 1 2) v3859_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3859_mb : Scalar.QComplex := ((-993047043068174332185032 : Int)/10^30,(-431476376165032505647816999 : Int)/10^30)
theorem v3859_mb_checked : Scalar.distance (sourceCoefficient 55 65 3 1) v3859_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3859_mg : Scalar.QComplex := ((-93086183136287587311601 : Int)/10^30,(214238748678645121111 : Int)/10^30)
theorem v3859_mg_checked : Scalar.distance (sourceCoefficient 55 65 3 2) v3859_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3859_upper : Scalar.QComplex := ((999994993098562340959042298774 : Int)/10^30,(-3164455372770498636477148812 : Int)/10^30)
theorem v3859_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 65 5) 1) 14) v3859_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3859 : Material (55 : Basis) (65 : Basis) where
  plus := ![v3859_pa,v3859_pb,v3859_pg]
  minus := ![(Primitive.Addresses.material3859 1).one,v3859_mb,v3859_mg]
  upper := v3859_upper
  lower := (Primitive.Addresses.material3859 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3859_pa_checked.trans (by decide +kernel)
    · exact v3859_pb_checked.trans (by decide +kernel)
    · exact v3859_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 65 Primitive.Addresses.material3859
    · exact v3859_mb_checked.trans (by decide +kernel)
    · exact v3859_mg_checked.trans (by decide +kernel)
  upper_error := v3859_upper_checked
  lower_error := reuse_lower_error 55 65 Primitive.Addresses.material3859

def v3860_pa : Scalar.QComplex := ((999998939831128773856460670281 : Int)/10^30,(-1456137568533362015923086385 : Int)/10^30)
theorem v3860_pa_checked : Scalar.distance (sourceCoefficient 55 66 1 0) v3860_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3860_pb : Scalar.QComplex := ((-628290624613549796308455 : Int)/10^30,(-431477061025359125065604301 : Int)/10^30)
theorem v3860_pb_checked : Scalar.distance (sourceCoefficient 55 66 1 1) v3860_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3860_pg : Scalar.QComplex := ((-93086330936056242646462 : Int)/10^30,(135546647295256875302 : Int)/10^30)
theorem v3860_pg_checked : Scalar.distance (sourceCoefficient 55 66 1 2) v3860_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3860_mb : Scalar.QComplex := ((-1000635661331679366464293 : Int)/10^30,(-431476358180217947272862104 : Int)/10^30)
theorem v3860_mb_checked : Scalar.distance (sourceCoefficient 55 66 3 1) v3860_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3860_mg : Scalar.QComplex := ((-93086179305109158231335 : Int)/10^30,(215875907970147637156 : Int)/10^30)
theorem v3860_mg_checked : Scalar.distance (sourceCoefficient 55 66 3 2) v3860_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3860_upper : Scalar.QComplex := ((999994937288832502276336531190 : Int)/10^30,(-3182042850740869866071185069 : Int)/10^30)
theorem v3860_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 66 5) 1) 14) v3860_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3860 : Material (55 : Basis) (66 : Basis) where
  plus := ![v3860_pa,v3860_pb,v3860_pg]
  minus := ![(Primitive.Addresses.material3860 1).one,v3860_mb,v3860_mg]
  upper := v3860_upper
  lower := (Primitive.Addresses.material3860 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3860_pa_checked.trans (by decide +kernel)
    · exact v3860_pb_checked.trans (by decide +kernel)
    · exact v3860_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 66 Primitive.Addresses.material3860
    · exact v3860_mb_checked.trans (by decide +kernel)
    · exact v3860_mg_checked.trans (by decide +kernel)
  upper_error := v3860_upper_checked
  lower_error := reuse_lower_error 55 66 Primitive.Addresses.material3860

def v3861_pa : Scalar.QComplex := ((999998896414459714068129769157 : Int)/10^30,(-1485654691599235320864492961 : Int)/10^30)
theorem v3861_pa_checked : Scalar.distance (sourceCoefficient 55 67 1 0) v3861_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3861_pb : Scalar.QComplex := ((-641026598348670873543672 : Int)/10^30,(-431477041432119513904220856 : Int)/10^30)
theorem v3861_pb_checked : Scalar.distance (sourceCoefficient 55 67 1 1) v3861_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3861_pg : Scalar.QComplex := ((-93086326801794170666782 : Int)/10^30,(138294290756404734643 : Int)/10^30)
theorem v3861_pg_checked : Scalar.distance (sourceCoefficient 55 67 1 2) v3861_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3861_mb : Scalar.QComplex := ((-1013371613416532021681604 : Int)/10^30,(-431476327596413905124289988 : Int)/10^30)
theorem v3861_mb_checked : Scalar.distance (sourceCoefficient 55 67 3 1) v3861_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3861_mg : Scalar.QComplex := ((-93086172799756067923469 : Int)/10^30,(218623546840540294536 : Int)/10^30)
theorem v3861_mg_checked : Scalar.distance (sourceCoefficient 55 67 3 2) v3861_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3861_upper : Scalar.QComplex := ((999994842928351467306090930249 : Int)/10^30,(-3211559854911223621490685951 : Int)/10^30)
theorem v3861_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 67 5) 1) 14) v3861_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3861 : Material (55 : Basis) (67 : Basis) where
  plus := ![v3861_pa,v3861_pb,v3861_pg]
  minus := ![(Primitive.Addresses.material3861 1).one,v3861_mb,v3861_mg]
  upper := v3861_upper
  lower := (Primitive.Addresses.material3861 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3861_pa_checked.trans (by decide +kernel)
    · exact v3861_pb_checked.trans (by decide +kernel)
    · exact v3861_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 67 Primitive.Addresses.material3861
    · exact v3861_mb_checked.trans (by decide +kernel)
    · exact v3861_mg_checked.trans (by decide +kernel)
  upper_error := v3861_upper_checked
  lower_error := reuse_lower_error 55 67 Primitive.Addresses.material3861

def v3862_pa : Scalar.QComplex := ((999998822174419255756521787088 : Int)/10^30,(-1534812618600520987035169244 : Int)/10^30)
theorem v3862_pa_checked : Scalar.distance (sourceCoefficient 55 68 1 0) v3862_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3862_pb : Scalar.QComplex := ((-662237136036862263711288 : Int)/10^30,(-431477007688968531889578632 : Int)/10^30)
theorem v3862_pb_checked : Scalar.distance (sourceCoefficient 55 68 1 1) v3862_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3862_pg : Scalar.QComplex := ((-93086319706571057656821 : Int)/10^30,(142870226380934963581 : Int)/10^30)
theorem v3862_pg_checked : Scalar.distance (sourceCoefficient 55 68 1 2) v3862_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3862_mb : Scalar.QComplex := ((-1034582114088251298701767 : Int)/10^30,(-431476275549536749473276860 : Int)/10^30)
theorem v3862_mb_checked : Scalar.distance (sourceCoefficient 55 68 3 1) v3862_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3862_mg : Scalar.QComplex := ((-93086161755709245309769 : Int)/10^30,(223199474638382570330 : Int)/10^30)
theorem v3862_mg_checked : Scalar.distance (sourceCoefficient 55 68 3 2) v3862_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3862_upper : Scalar.QComplex := ((999994683846299148896127610611 : Int)/10^30,(-3260717580565976687801715054 : Int)/10^30)
theorem v3862_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 68 5) 1) 14) v3862_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3862 : Material (55 : Basis) (68 : Basis) where
  plus := ![v3862_pa,v3862_pb,v3862_pg]
  minus := ![(Primitive.Addresses.material3862 1).one,v3862_mb,v3862_mg]
  upper := v3862_upper
  lower := (Primitive.Addresses.material3862 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3862_pa_checked.trans (by decide +kernel)
    · exact v3862_pb_checked.trans (by decide +kernel)
    · exact v3862_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 68 Primitive.Addresses.material3862
    · exact v3862_mb_checked.trans (by decide +kernel)
    · exact v3862_mg_checked.trans (by decide +kernel)
  upper_error := v3862_upper_checked
  lower_error := reuse_lower_error 55 68 Primitive.Addresses.material3862

def v3863_pa : Scalar.QComplex := ((999998788734108376905157932005 : Int)/10^30,(-1556447980525250151427856262 : Int)/10^30)
theorem v3863_pa_checked : Scalar.distance (sourceCoefficient 55 69 1 0) v3863_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3863_pb : Scalar.QComplex := ((-671572306912625019320867 : Int)/10^30,(-431476992397370416341874100 : Int)/10^30)
theorem v3863_pb_checked : Scalar.distance (sourceCoefficient 55 69 1 1) v3863_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3863_pg : Scalar.QComplex := ((-93086316500656192574162 : Int)/10^30,(144884184825251915888 : Int)/10^30)
theorem v3863_pg_checked : Scalar.distance (sourceCoefficient 55 69 1 2) v3863_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3863_mb : Scalar.QComplex := ((-1043917268292142833174898 : Int)/10^30,(-431476252202112302391912988 : Int)/10^30)
theorem v3863_mb_checked : Scalar.distance (sourceCoefficient 55 69 3 1) v3863_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3863_mg : Scalar.QComplex := ((-93086156811840141811394 : Int)/10^30,(225213429566250611850 : Int)/10^30)
theorem v3863_mg_checked : Scalar.distance (sourceCoefficient 55 69 3 2) v3863_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3863_upper : Scalar.QComplex := ((999994613065366138078796430066 : Int)/10^30,(-3282352852552432837858047557 : Int)/10^30)
theorem v3863_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 69 5) 1) 14) v3863_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3863 : Material (55 : Basis) (69 : Basis) where
  plus := ![v3863_pa,v3863_pb,v3863_pg]
  minus := ![(Primitive.Addresses.material3863 1).one,v3863_mb,v3863_mg]
  upper := v3863_upper
  lower := (Primitive.Addresses.material3863 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3863_pa_checked.trans (by decide +kernel)
    · exact v3863_pb_checked.trans (by decide +kernel)
    · exact v3863_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 69 Primitive.Addresses.material3863
    · exact v3863_mb_checked.trans (by decide +kernel)
    · exact v3863_mg_checked.trans (by decide +kernel)
  upper_error := v3863_upper_checked
  lower_error := reuse_lower_error 55 69 Primitive.Addresses.material3863

def v3864_pa : Scalar.QComplex := ((999998766481519074233509982527 : Int)/10^30,(-1570679929292944837629799627 : Int)/10^30)
theorem v3864_pa_checked : Scalar.distance (sourceCoefficient 55 70 1 0) v3864_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3864_pb : Scalar.QComplex := ((-677713071851794791166549 : Int)/10^30,(-431476982191574781698693372 : Int)/10^30)
theorem v3864_pb_checked : Scalar.distance (sourceCoefficient 55 70 1 1) v3864_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3864_pg : Scalar.QComplex := ((-93086314364056244608914 : Int)/10^30,(146208986014963024555 : Int)/10^30)
theorem v3864_pg_checked : Scalar.distance (sourceCoefficient 55 70 1 2) v3864_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3864_mb : Scalar.QComplex := ((-1050058022137683190620955 : Int)/10^30,(-431476236697116895115468991 : Int)/10^30)
theorem v3864_mb_checked : Scalar.distance (sourceCoefficient 55 70 3 1) v3864_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3864_mg : Scalar.QComplex := ((-93086153531997229509915 : Int)/10^30,(226538228418888164977 : Int)/10^30)
theorem v3864_mg_checked : Scalar.distance (sourceCoefficient 55 70 3 2) v3864_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3864_upper : Scalar.QComplex := ((999994566249757517290503069618 : Int)/10^30,(-3296584741717361239439453665 : Int)/10^30)
theorem v3864_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 70 5) 1) 14) v3864_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3864 : Material (55 : Basis) (70 : Basis) where
  plus := ![v3864_pa,v3864_pb,v3864_pg]
  minus := ![(Primitive.Addresses.material3864 1).one,v3864_mb,v3864_mg]
  upper := v3864_upper
  lower := (Primitive.Addresses.material3864 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3864_pa_checked.trans (by decide +kernel)
    · exact v3864_pb_checked.trans (by decide +kernel)
    · exact v3864_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 70 Primitive.Addresses.material3864
    · exact v3864_mb_checked.trans (by decide +kernel)
    · exact v3864_mg_checked.trans (by decide +kernel)
  upper_error := v3864_upper_checked
  lower_error := reuse_lower_error 55 70 Primitive.Addresses.material3864

def v3865_pa : Scalar.QComplex := ((999998728030209660903429321573 : Int)/10^30,(-1594972715368838403901951749 : Int)/10^30)
theorem v3865_pa_checked : Scalar.distance (sourceCoefficient 55 71 1 0) v3865_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3865_pb : Scalar.QComplex := ((-688194861053773044431600 : Int)/10^30,(-431476964501900361670365405 : Int)/10^30)
theorem v3865_pb_checked : Scalar.distance (sourceCoefficient 55 71 1 1) v3865_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3865_pg : Scalar.QComplex := ((-93086310666234380917270 : Int)/10^30,(148470314536745968494 : Int)/10^30)
theorem v3865_pg_checked : Scalar.distance (sourceCoefficient 55 71 1 2) v3865_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3865_mb : Scalar.QComplex := ((-1060539792171419971433886 : Int)/10^30,(-431476209962137062715292913 : Int)/10^30)
theorem v3865_mb_checked : Scalar.distance (sourceCoefficient 55 71 3 1) v3865_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3865_mg : Scalar.QComplex := ((-93086147882752074843572 : Int)/10^30,(228799552907621427785 : Int)/10^30)
theorem v3865_mg_checked : Scalar.distance (sourceCoefficient 55 71 3 2) v3865_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3865_upper : Scalar.QComplex := ((999994485871360430014164175584 : Int)/10^30,(-3320877425248531804910610429 : Int)/10^30)
theorem v3865_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 71 5) 1) 14) v3865_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3865 : Material (55 : Basis) (71 : Basis) where
  plus := ![v3865_pa,v3865_pb,v3865_pg]
  minus := ![(Primitive.Addresses.material3865 1).one,v3865_mb,v3865_mg]
  upper := v3865_upper
  lower := (Primitive.Addresses.material3865 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3865_pa_checked.trans (by decide +kernel)
    · exact v3865_pb_checked.trans (by decide +kernel)
    · exact v3865_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 71 Primitive.Addresses.material3865
    · exact v3865_mb_checked.trans (by decide +kernel)
    · exact v3865_mg_checked.trans (by decide +kernel)
  upper_error := v3865_upper_checked
  lower_error := reuse_lower_error 55 71 Primitive.Addresses.material3865

def v3866_pa : Scalar.QComplex := ((999998685635046628068412788211 : Int)/10^30,(-1621335307451432922758121325 : Int)/10^30)
theorem v3866_pa_checked : Scalar.distance (sourceCoefficient 55 72 1 0) v3866_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3866_pb : Scalar.QComplex := ((-699569724641441889338589 : Int)/10^30,(-431476944920888275102750464 : Int)/10^30)
theorem v3866_pb_checked : Scalar.distance (sourceCoefficient 55 72 1 1) v3866_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3866_pg : Scalar.QComplex := ((-93086306580835459104619 : Int)/10^30,(150924313869385964479 : Int)/10^30)
theorem v3866_pg_checked : Scalar.distance (sourceCoefficient 55 72 1 2) v3866_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3866_mb : Scalar.QComplex := ((-1071914634626175711043360 : Int)/10^30,(-431476180565137295733500180 : Int)/10^30)
theorem v3866_mb_checked : Scalar.distance (sourceCoefficient 55 72 3 1) v3866_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3866_mg : Scalar.QComplex := ((-93086141679663774170432 : Int)/10^30,(231253547801010048931 : Int)/10^30)
theorem v3866_mg_checked : Scalar.distance (sourceCoefficient 55 72 3 2) v3866_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3866_upper : Scalar.QComplex := ((999994397976818200907872655263 : Int)/10^30,(-3347239904896936848817659984 : Int)/10^30)
theorem v3866_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 72 5) 1) 14) v3866_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3866 : Material (55 : Basis) (72 : Basis) where
  plus := ![v3866_pa,v3866_pb,v3866_pg]
  minus := ![(Primitive.Addresses.material3866 1).one,v3866_mb,v3866_mg]
  upper := v3866_upper
  lower := (Primitive.Addresses.material3866 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3866_pa_checked.trans (by decide +kernel)
    · exact v3866_pb_checked.trans (by decide +kernel)
    · exact v3866_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 72 Primitive.Addresses.material3866
    · exact v3866_mb_checked.trans (by decide +kernel)
    · exact v3866_mg_checked.trans (by decide +kernel)
  upper_error := v3866_upper_checked
  lower_error := reuse_lower_error 55 72 Primitive.Addresses.material3866

def v3867_pa : Scalar.QComplex := ((999998670269359574874278878656 : Int)/10^30,(-1630784937588851829541073065 : Int)/10^30)
theorem v3867_pa_checked : Scalar.distance (sourceCoefficient 55 73 1 0) v3867_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3867_pb : Scalar.QComplex := ((-703647026749975603675917 : Int)/10^30,(-431476937804759786031906152 : Int)/10^30)
theorem v3867_pb_checked : Scalar.distance (sourceCoefficient 55 73 1 1) v3867_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3867_pg : Scalar.QComplex := ((-93086305098054578397297 : Int)/10^30,(151803946108066232857 : Int)/10^30)
theorem v3867_pg_checked : Scalar.distance (sourceCoefficient 55 73 1 2) v3867_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3867_mb : Scalar.QComplex := ((-1075991929075645120923294 : Int)/10^30,(-431476169930483371528041566 : Int)/10^30)
theorem v3867_mb_checked : Scalar.distance (sourceCoefficient 55 73 3 1) v3867_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3867_mg : Scalar.QComplex := ((-93086139437800440754499 : Int)/10^30,(232133178432589915591 : Int)/10^30)
theorem v3867_mg_checked : Scalar.distance (sourceCoefficient 55 73 3 2) v3867_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3867_upper : Scalar.QComplex := ((999994366301949679664080706348 : Int)/10^30,(-3356689494440459807873893051 : Int)/10^30)
theorem v3867_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 73 5) 1) 14) v3867_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3867 : Material (55 : Basis) (73 : Basis) where
  plus := ![v3867_pa,v3867_pb,v3867_pg]
  minus := ![(Primitive.Addresses.material3867 1).one,v3867_mb,v3867_mg]
  upper := v3867_upper
  lower := (Primitive.Addresses.material3867 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3867_pa_checked.trans (by decide +kernel)
    · exact v3867_pb_checked.trans (by decide +kernel)
    · exact v3867_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 73 Primitive.Addresses.material3867
    · exact v3867_mb_checked.trans (by decide +kernel)
    · exact v3867_mg_checked.trans (by decide +kernel)
  upper_error := v3867_upper_checked
  lower_error := reuse_lower_error 55 73 Primitive.Addresses.material3867

def v3868_pa : Scalar.QComplex := ((999998652872412808989968803667 : Int)/10^30,(-1641418094097077964619691628 : Int)/10^30)
theorem v3868_pa_checked : Scalar.distance (sourceCoefficient 55 74 1 0) v3868_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3868_pb : Scalar.QComplex := ((-708234993736923512094170 : Int)/10^30,(-431476929735939862810589727 : Int)/10^30)
theorem v3868_pb_checked : Scalar.distance (sourceCoefficient 55 74 1 1) v3868_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3868_pg : Scalar.QComplex := ((-93086303417966100938239 : Int)/10^30,(152793748575534088058 : Int)/10^30)
theorem v3868_pg_checked : Scalar.distance (sourceCoefficient 55 74 1 2) v3868_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3868_mb : Scalar.QComplex := ((-1080579887391255052070188 : Int)/10^30,(-431476157902457577323564917 : Int)/10^30)
theorem v3868_mb_checked : Scalar.distance (sourceCoefficient 55 74 3 1) v3868_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3868_mg : Scalar.QComplex := ((-93086136903557638492689 : Int)/10^30,(233122979081668388275 : Int)/10^30)
theorem v3868_mg_checked : Scalar.distance (sourceCoefficient 55 74 3 2) v3868_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3868_upper : Scalar.QComplex := ((999994330553165323713211659269 : Int)/10^30,(-3367322605086296503020457848 : Int)/10^30)
theorem v3868_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 74 5) 1) 14) v3868_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3868 : Material (55 : Basis) (74 : Basis) where
  plus := ![v3868_pa,v3868_pb,v3868_pg]
  minus := ![(Primitive.Addresses.material3868 1).one,v3868_mb,v3868_mg]
  upper := v3868_upper
  lower := (Primitive.Addresses.material3868 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3868_pa_checked.trans (by decide +kernel)
    · exact v3868_pb_checked.trans (by decide +kernel)
    · exact v3868_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 74 Primitive.Addresses.material3868
    · exact v3868_mb_checked.trans (by decide +kernel)
    · exact v3868_mg_checked.trans (by decide +kernel)
  upper_error := v3868_upper_checked
  lower_error := reuse_lower_error 55 74 Primitive.Addresses.material3868

def v3869_pa : Scalar.QComplex := ((999998628444848224350077596834 : Int)/10^30,(-1656233202899810689120148185 : Int)/10^30)
theorem v3869_pa_checked : Scalar.distance (sourceCoefficient 55 75 1 0) v3869_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3869_pb : Scalar.QComplex := ((-714627378665412821243436 : Int)/10^30,(-431476918385254342640953345 : Int)/10^30)
theorem v3869_pb_checked : Scalar.distance (sourceCoefficient 55 75 1 1) v3869_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3869_pg : Scalar.QComplex := ((-93086301056637242736849 : Int)/10^30,(154172834001675071441 : Int)/10^30)
theorem v3869_pg_checked : Scalar.distance (sourceCoefficient 55 75 1 2) v3869_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3869_mb : Scalar.QComplex := ((-1086972260144436917911532 : Int)/10^30,(-431476141035435992576368164 : Int)/10^30)
theorem v3869_mb_checked : Scalar.distance (sourceCoefficient 55 75 3 1) v3869_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3869_mg : Scalar.QComplex := ((-93086133352141048464180 : Int)/10^30,(234502061956592385865 : Int)/10^30)
theorem v3869_mg_checked : Scalar.distance (sourceCoefficient 55 75 3 2) v3869_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3869_upper : Scalar.QComplex := ((999994280556103343716329221795 : Int)/10^30,(-3382137649663904549040067044 : Int)/10^30)
theorem v3869_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 75 5) 1) 14) v3869_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3869 : Material (55 : Basis) (75 : Basis) where
  plus := ![v3869_pa,v3869_pb,v3869_pg]
  minus := ![(Primitive.Addresses.material3869 1).one,v3869_mb,v3869_mg]
  upper := v3869_upper
  lower := (Primitive.Addresses.material3869 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3869_pa_checked.trans (by decide +kernel)
    · exact v3869_pb_checked.trans (by decide +kernel)
    · exact v3869_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 75 Primitive.Addresses.material3869
    · exact v3869_mb_checked.trans (by decide +kernel)
    · exact v3869_mg_checked.trans (by decide +kernel)
  upper_error := v3869_upper_checked
  lower_error := reuse_lower_error 55 75 Primitive.Addresses.material3869

def v3870_pa : Scalar.QComplex := ((999998607780308519048601759622 : Int)/10^30,(-1668663370691114993639376590 : Int)/10^30)
theorem v3870_pa_checked : Scalar.distance (sourceCoefficient 55 76 1 0) v3870_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3870_pb : Scalar.QComplex := ((-719990715339418710715480 : Int)/10^30,(-431476908764388452216233069 : Int)/10^30)
theorem v3870_pb_checked : Scalar.distance (sourceCoefficient 55 76 1 1) v3870_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3870_pg : Scalar.QComplex := ((-93086299057046240362871 : Int)/10^30,(155329913803056611325 : Int)/10^30)
theorem v3870_pg_checked : Scalar.distance (sourceCoefficient 55 76 1 2) v3870_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3870_mb : Scalar.QComplex := ((-1092335586519053491334209 : Int)/10^30,(-431476126786255690489459092 : Int)/10^30)
theorem v3870_mb_checked : Scalar.distance (sourceCoefficient 55 76 3 1) v3870_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3870_mg : Scalar.QComplex := ((-93086130354043034976780 : Int)/10^30,(235659139601583257721 : Int)/10^30)
theorem v3870_mg_checked : Scalar.distance (sourceCoefficient 55 76 3 2) v3870_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3870_upper : Scalar.QComplex := ((999994238438252464041349241464 : Int)/10^30,(-3394567763276813219537829713 : Int)/10^30)
theorem v3870_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 76 5) 1) 14) v3870_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3870 : Material (55 : Basis) (76 : Basis) where
  plus := ![v3870_pa,v3870_pb,v3870_pg]
  minus := ![(Primitive.Addresses.material3870 1).one,v3870_mb,v3870_mg]
  upper := v3870_upper
  lower := (Primitive.Addresses.material3870 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3870_pa_checked.trans (by decide +kernel)
    · exact v3870_pb_checked.trans (by decide +kernel)
    · exact v3870_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 76 Primitive.Addresses.material3870
    · exact v3870_mb_checked.trans (by decide +kernel)
    · exact v3870_mg_checked.trans (by decide +kernel)
  upper_error := v3870_upper_checked
  lower_error := reuse_lower_error 55 76 Primitive.Addresses.material3870

def v3871_pa : Scalar.QComplex := ((999998602974266343062081527391 : Int)/10^30,(-1671541060109794412476927016 : Int)/10^30)
theorem v3871_pa_checked : Scalar.distance (sourceCoefficient 55 77 1 0) v3871_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3871_pb : Scalar.QComplex := ((-721232373324883790436839 : Int)/10^30,(-431476906524404824167054301 : Int)/10^30)
theorem v3871_pb_checked : Scalar.distance (sourceCoefficient 55 77 1 1) v3871_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3871_pg : Scalar.QComplex := ((-93086298591731929410677 : Int)/10^30,(155597787603833834629 : Int)/10^30)
theorem v3871_pg_checked : Scalar.distance (sourceCoefficient 55 77 1 2) v3871_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3871_mb : Scalar.QComplex := ((-1093577242109187570604780 : Int)/10^30,(-431476123474777977231929270 : Int)/10^30)
theorem v3871_mb_checked : Scalar.distance (sourceCoefficient 55 77 3 1) v3871_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3871_mg : Scalar.QComplex := ((-93086129657565871799756 : Int)/10^30,(235927012901073529185 : Int)/10^30)
theorem v3871_mg_checked : Scalar.distance (sourceCoefficient 55 77 3 2) v3871_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3871_upper : Scalar.QComplex := ((999994228665586571394174453705 : Int)/10^30,(-3397445440114719491384938864 : Int)/10^30)
theorem v3871_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 77 5) 1) 14) v3871_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3871 : Material (55 : Basis) (77 : Basis) where
  plus := ![v3871_pa,v3871_pb,v3871_pg]
  minus := ![(Primitive.Addresses.material3871 1).one,v3871_mb,v3871_mg]
  upper := v3871_upper
  lower := (Primitive.Addresses.material3871 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3871_pa_checked.trans (by decide +kernel)
    · exact v3871_pb_checked.trans (by decide +kernel)
    · exact v3871_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 77 Primitive.Addresses.material3871
    · exact v3871_mb_checked.trans (by decide +kernel)
    · exact v3871_mg_checked.trans (by decide +kernel)
  upper_error := v3871_upper_checked
  lower_error := reuse_lower_error 55 77 Primitive.Addresses.material3871

def v3872_pa : Scalar.QComplex := ((999998573907654900156326461288 : Int)/10^30,(-1688840624943724698623540947 : Int)/10^30)
theorem v3872_pa_checked : Scalar.distance (sourceCoefficient 55 78 1 0) v3872_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3872_pb : Scalar.QComplex := ((-728696744740941888765948 : Int)/10^30,(-431476892958075192395461463 : Int)/10^30)
theorem v3872_pb_checked : Scalar.distance (sourceCoefficient 55 78 1 1) v3872_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3872_pg : Scalar.QComplex := ((-93086295775486747843448 : Int)/10^30,(157208142124497510673 : Int)/10^30)
theorem v3872_pg_checked : Scalar.distance (sourceCoefficient 55 78 1 2) v3872_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3872_mb : Scalar.QComplex := ((-1101041599038787584695320 : Int)/10^30,(-431476103467037047575618154 : Int)/10^30)
theorem v3872_mb_checked : Scalar.distance (sourceCoefficient 55 78 3 1) v3872_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3872_mg : Scalar.QComplex := ((-93086125451658315191820 : Int)/10^30,(237537364391835867631 : Int)/10^30)
theorem v3872_mg_checked : Scalar.distance (sourceCoefficient 55 78 3 2) v3872_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3872_upper : Scalar.QComplex := ((999994169741538920690306519241 : Int)/10^30,(-3414744929016645658964927219 : Int)/10^30)
theorem v3872_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 55 78 5) 1) 14) v3872_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3872 : Material (55 : Basis) (78 : Basis) where
  plus := ![v3872_pa,v3872_pb,v3872_pg]
  minus := ![(Primitive.Addresses.material3872 1).one,v3872_mb,v3872_mg]
  upper := v3872_upper
  lower := (Primitive.Addresses.material3872 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3872_pa_checked.trans (by decide +kernel)
    · exact v3872_pb_checked.trans (by decide +kernel)
    · exact v3872_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 55 78 Primitive.Addresses.material3872
    · exact v3872_mb_checked.trans (by decide +kernel)
    · exact v3872_mg_checked.trans (by decide +kernel)
  upper_error := v3872_upper_checked
  lower_error := reuse_lower_error 55 78 Primitive.Addresses.material3872

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
