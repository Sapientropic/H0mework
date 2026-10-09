import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B150
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B151

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3617_pa : Scalar.QComplex := ((999998237164017340539241923345 : Int)/10^30,(-1877676451822363286786089158 : Int)/10^30)
theorem v3617_pa_checked : Scalar.distance (sourceCoefficient 49 90 1 0) v3617_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3617_pb : Scalar.QComplex := ((-810175109243346108079159 : Int)/10^30,(-431476722334779211276498916 : Int)/10^30)
theorem v3617_pb_checked : Scalar.distance (sourceCoefficient 49 90 1 1) v3617_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3617_pg : Scalar.QComplex := ((-93086261697325185310792 : Int)/10^30,(174786189696625983426 : Int)/10^30)
theorem v3617_pg_checked : Scalar.distance (sourceCoefficient 49 90 1 2) v3617_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3617_mb : Scalar.QComplex := ((-1182519785962853110828944 : Int)/10^30,(-431475862531645681046180477 : Int)/10^30)
theorem v3617_mb_checked : Scalar.distance (sourceCoefficient 49 90 3 1) v3617_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3617_mg : Scalar.QComplex := ((-93086076204446072643179 : Int)/10^30,(255115376010935267776 : Int)/10^30)
theorem v3617_mg_checked : Scalar.distance (sourceCoefficient 49 90 3 2) v3617_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3617_upper : Scalar.QComplex := ((999993507084896761028470130137 : Int)/10^30,(-3603579893457533042099542676 : Int)/10^30)
theorem v3617_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 90 5) 1) 14) v3617_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3617 : Material (49 : Basis) (90 : Basis) where
  plus := ![v3617_pa,v3617_pb,v3617_pg]
  minus := ![(Primitive.Addresses.material3617 1).one,v3617_mb,v3617_mg]
  upper := v3617_upper
  lower := (Primitive.Addresses.material3617 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3617_pa_checked.trans (by decide +kernel)
    · exact v3617_pb_checked.trans (by decide +kernel)
    · exact v3617_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 90 Primitive.Addresses.material3617
    · exact v3617_mb_checked.trans (by decide +kernel)
    · exact v3617_mg_checked.trans (by decide +kernel)
  upper_error := v3617_upper_checked
  lower_error := reuse_lower_error 49 90 Primitive.Addresses.material3617

def v3618_pa : Scalar.QComplex := ((999998209338557527636246927699 : Int)/10^30,(-1892437496583790993696657376 : Int)/10^30)
theorem v3618_pa_checked : Scalar.distance (sourceCoefficient 49 91 1 0) v3618_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3618_pb : Scalar.QComplex := ((-816544164731039107663451 : Int)/10^30,(-431476708768929946957876652 : Int)/10^30)
theorem v3618_pb_checked : Scalar.distance (sourceCoefficient 49 91 1 1) v3618_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3618_pg : Scalar.QComplex := ((-93086258938899005919135 : Int)/10^30,(176160242276034111648 : Int)/10^30)
theorem v3618_pg_checked : Scalar.distance (sourceCoefficient 49 91 1 2) v3618_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3618_mb : Scalar.QComplex := ((-1188888827372338740192823 : Int)/10^30,(-431475843469593433644903984 : Int)/10^30)
theorem v3618_mb_checked : Scalar.distance (sourceCoefficient 49 91 3 1) v3618_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3618_mg : Scalar.QComplex := ((-93086072260275429341337 : Int)/10^30,(256489425698323265468 : Int)/10^30)
theorem v3618_mg_checked : Scalar.distance (sourceCoefficient 49 91 3 2) v3618_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3618_upper : Scalar.QComplex := ((999993453783254244175227793861 : Int)/10^30,(-3618340868209899199909713317 : Int)/10^30)
theorem v3618_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 91 5) 1) 14) v3618_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3618 : Material (49 : Basis) (91 : Basis) where
  plus := ![v3618_pa,v3618_pb,v3618_pg]
  minus := ![(Primitive.Addresses.material3618 1).one,v3618_mb,v3618_mg]
  upper := v3618_upper
  lower := (Primitive.Addresses.material3618 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3618_pa_checked.trans (by decide +kernel)
    · exact v3618_pb_checked.trans (by decide +kernel)
    · exact v3618_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 91 Primitive.Addresses.material3618
    · exact v3618_mb_checked.trans (by decide +kernel)
    · exact v3618_mg_checked.trans (by decide +kernel)
  upper_error := v3618_upper_checked
  lower_error := reuse_lower_error 49 91 Primitive.Addresses.material3618

def v3619_pa : Scalar.QComplex := ((999998148353031477210937170308 : Int)/10^30,(-1924393543028317814051195636 : Int)/10^30)
theorem v3619_pa_checked : Scalar.distance (sourceCoefficient 49 92 1 0) v3619_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3619_pb : Scalar.QComplex := ((-830332472461538380892302 : Int)/10^30,(-431476678970915880427063907 : Int)/10^30)
theorem v3619_pb_checked : Scalar.distance (sourceCoefficient 49 92 1 1) v3619_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3619_pg : Scalar.QComplex := ((-93086252886143094857831 : Int)/10^30,(179134915693418485422 : Int)/10^30)
theorem v3619_pg_checked : Scalar.distance (sourceCoefficient 49 92 1 2) v3619_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3619_mb : Scalar.QComplex := ((-1202677104254476801881260 : Int)/10^30,(-431475801772901893183183621 : Int)/10^30)
theorem v3619_mb_checked : Scalar.distance (sourceCoefficient 49 92 3 1) v3619_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3619_mg : Scalar.QComplex := ((-93086063640512587112326 : Int)/10^30,(259464092784845031419 : Int)/10^30)
theorem v3619_mg_checked : Scalar.distance (sourceCoefficient 49 92 3 2) v3619_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3619_upper : Scalar.QComplex := ((999993337644581891161283856331 : Int)/10^30,(-3650296761804163262719657374 : Int)/10^30)
theorem v3619_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 92 5) 1) 14) v3619_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3619 : Material (49 : Basis) (92 : Basis) where
  plus := ![v3619_pa,v3619_pb,v3619_pg]
  minus := ![(Primitive.Addresses.material3619 1).one,v3619_mb,v3619_mg]
  upper := v3619_upper
  lower := (Primitive.Addresses.material3619 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3619_pa_checked.trans (by decide +kernel)
    · exact v3619_pb_checked.trans (by decide +kernel)
    · exact v3619_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 92 Primitive.Addresses.material3619
    · exact v3619_mb_checked.trans (by decide +kernel)
    · exact v3619_mg_checked.trans (by decide +kernel)
  upper_error := v3619_upper_checked
  lower_error := reuse_lower_error 49 92 Primitive.Addresses.material3619

def v3620_pa : Scalar.QComplex := ((999998074650054544175565454388 : Int)/10^30,(-1962319083110398843156159201 : Int)/10^30)
theorem v3620_pa_checked : Scalar.distance (sourceCoefficient 49 93 1 0) v3620_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3620_pb : Scalar.QComplex := ((-846696480356547247382546 : Int)/10^30,(-431476642844170135936490087 : Int)/10^30)
theorem v3620_pb_checked : Scalar.distance (sourceCoefficient 49 93 1 1) v3620_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3620_pg : Scalar.QComplex := ((-93086245558799736386275 : Int)/10^30,(182665267729696595155 : Int)/10^30)
theorem v3620_pg_checked : Scalar.distance (sourceCoefficient 49 93 1 2) v3620_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3620_mb : Scalar.QComplex := ((-1219041074880663167685882 : Int)/10^30,(-431475751524767794495057217 : Int)/10^30)
theorem v3620_mb_checked : Scalar.distance (sourceCoefficient 49 93 3 1) v3620_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3620_mg : Scalar.QComplex := ((-93086053266637150790884 : Int)/10^30,(262994437183444425919 : Int)/10^30)
theorem v3620_mg_checked : Scalar.distance (sourceCoefficient 49 93 3 2) v3620_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3620_upper : Scalar.QComplex := ((999993198485673126500362863800 : Int)/10^30,(-3688222118195955481870890446 : Int)/10^30)
theorem v3620_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 93 5) 1) 14) v3620_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3620 : Material (49 : Basis) (93 : Basis) where
  plus := ![v3620_pa,v3620_pb,v3620_pg]
  minus := ![(Primitive.Addresses.material3620 1).one,v3620_mb,v3620_mg]
  upper := v3620_upper
  lower := (Primitive.Addresses.material3620 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3620_pa_checked.trans (by decide +kernel)
    · exact v3620_pb_checked.trans (by decide +kernel)
    · exact v3620_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 93 Primitive.Addresses.material3620
    · exact v3620_mb_checked.trans (by decide +kernel)
    · exact v3620_mg_checked.trans (by decide +kernel)
  upper_error := v3620_upper_checked
  lower_error := reuse_lower_error 49 93 Primitive.Addresses.material3620

def v3621_pa : Scalar.QComplex := ((999997985737536857008133030461 : Int)/10^30,(-2007117552370242540465145791 : Int)/10^30)
theorem v3621_pa_checked : Scalar.distance (sourceCoefficient 49 94 1 0) v3621_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3621_pb : Scalar.QComplex := ((-866025999903244200074709 : Int)/10^30,(-431476599104460174084469205 : Int)/10^30)
theorem v3621_pb_checked : Scalar.distance (sourceCoefficient 49 94 1 1) v3621_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3621_pg : Scalar.QComplex := ((-93086236702349680486761 : Int)/10^30,(186835395904901885809 : Int)/10^30)
theorem v3621_pg_checked : Scalar.distance (sourceCoefficient 49 94 1 2) v3621_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3621_mb : Scalar.QComplex := ((-1238370549484696856788416 : Int)/10^30,(-431475691104569319379922299 : Int)/10^30)
theorem v3621_mb_checked : Scalar.distance (sourceCoefficient 49 94 3 1) v3621_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3621_mg : Scalar.QComplex := ((-93086040811557592951288 : Int)/10^30,(267164556163202894135 : Int)/10^30)
theorem v3621_mg_checked : Scalar.distance (sourceCoefficient 49 94 3 2) v3621_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3621_upper : Scalar.QComplex := ((999993032255194006977766129975 : Int)/10^30,(-3733020367278802167050066665 : Int)/10^30)
theorem v3621_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 94 5) 1) 14) v3621_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3621 : Material (49 : Basis) (94 : Basis) where
  plus := ![v3621_pa,v3621_pb,v3621_pg]
  minus := ![(Primitive.Addresses.material3621 1).one,v3621_mb,v3621_mg]
  upper := v3621_upper
  lower := (Primitive.Addresses.material3621 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3621_pa_checked.trans (by decide +kernel)
    · exact v3621_pb_checked.trans (by decide +kernel)
    · exact v3621_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 94 Primitive.Addresses.material3621
    · exact v3621_mb_checked.trans (by decide +kernel)
    · exact v3621_mg_checked.trans (by decide +kernel)
  upper_error := v3621_upper_checked
  lower_error := reuse_lower_error 49 94 Primitive.Addresses.material3621

def v3622_pa : Scalar.QComplex := ((999997895893863965792474015357 : Int)/10^30,(-2051391684882675777286407245 : Int)/10^30)
theorem v3622_pa_checked : Scalar.distance (sourceCoefficient 49 95 1 0) v3622_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3622_pb : Scalar.QComplex := ((-885129279026132519127215 : Int)/10^30,(-431476554742303144370926939 : Int)/10^30)
theorem v3622_pb_checked : Scalar.distance (sourceCoefficient 49 95 1 1) v3622_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3622_pg : Scalar.QComplex := ((-93086227735417683334580 : Int)/10^30,(190956715346727424267 : Int)/10^30)
theorem v3622_pg_checked : Scalar.distance (sourceCoefficient 49 95 1 2) v3622_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3622_mb : Scalar.QComplex := ((-1257473783212017776144180 : Int)/10^30,(-431475630257159304425170753 : Int)/10^30)
theorem v3622_mb_checked : Scalar.distance (sourceCoefficient 49 95 3 1) v3622_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3622_mg : Scalar.QComplex := ((-93086028288115873639479 : Int)/10^30,(271285866332414392880 : Int)/10^30)
theorem v3622_mg_checked : Scalar.distance (sourceCoefficient 49 95 3 2) v3622_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3622_upper : Scalar.QComplex := ((999992865998518728825544377299 : Int)/10^30,(-3777294278788086975641380606 : Int)/10^30)
theorem v3622_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 95 5) 1) 14) v3622_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3622 : Material (49 : Basis) (95 : Basis) where
  plus := ![v3622_pa,v3622_pb,v3622_pg]
  minus := ![(Primitive.Addresses.material3622 1).one,v3622_mb,v3622_mg]
  upper := v3622_upper
  lower := (Primitive.Addresses.material3622 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3622_pa_checked.trans (by decide +kernel)
    · exact v3622_pb_checked.trans (by decide +kernel)
    · exact v3622_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 95 Primitive.Addresses.material3622
    · exact v3622_mb_checked.trans (by decide +kernel)
    · exact v3622_mg_checked.trans (by decide +kernel)
  upper_error := v3622_upper_checked
  lower_error := reuse_lower_error 49 95 Primitive.Addresses.material3622

def v3623_pa : Scalar.QComplex := ((999997852046792489502840266766 : Int)/10^30,(-2072655736324296733263286791 : Int)/10^30)
theorem v3623_pa_checked : Scalar.distance (sourceCoefficient 49 96 1 0) v3623_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3623_pb : Scalar.QComplex := ((-894304232208163607842748 : Int)/10^30,(-431476533035099812621372687 : Int)/10^30)
theorem v3623_pb_checked : Scalar.distance (sourceCoefficient 49 96 1 1) v3623_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3623_pg : Scalar.QComplex := ((-93086223353091325874948 : Int)/10^30,(192936109223284098800 : Int)/10^30)
theorem v3623_pg_checked : Scalar.distance (sourceCoefficient 49 96 1 2) v3623_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3623_mb : Scalar.QComplex := ((-1266648714245455659960381 : Int)/10^30,(-431475600632392683718357828 : Int)/10^30)
theorem v3623_mb_checked : Scalar.distance (sourceCoefficient 49 96 3 1) v3623_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3623_mg : Scalar.QComplex := ((-93086022197663381042671 : Int)/10^30,(273265255690201990567 : Int)/10^30)
theorem v3623_mg_checked : Scalar.distance (sourceCoefficient 49 96 3 2) v3623_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3623_upper : Scalar.QComplex := ((999992785451688829038262329731 : Int)/10^30,(-3798558222883333567446384039 : Int)/10^30)
theorem v3623_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 96 5) 1) 14) v3623_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3623 : Material (49 : Basis) (96 : Basis) where
  plus := ![v3623_pa,v3623_pb,v3623_pg]
  minus := ![(Primitive.Addresses.material3623 1).one,v3623_mb,v3623_mg]
  upper := v3623_upper
  lower := (Primitive.Addresses.material3623 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3623_pa_checked.trans (by decide +kernel)
    · exact v3623_pb_checked.trans (by decide +kernel)
    · exact v3623_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 96 Primitive.Addresses.material3623
    · exact v3623_mb_checked.trans (by decide +kernel)
    · exact v3623_mg_checked.trans (by decide +kernel)
  upper_error := v3623_upper_checked
  lower_error := reuse_lower_error 49 96 Primitive.Addresses.material3623

def v3624_pa : Scalar.QComplex := ((999997697730341104984438695417 : Int)/10^30,(-2145817796865439564396472194 : Int)/10^30)
theorem v3624_pa_checked : Scalar.distance (sourceCoefficient 49 97 1 0) v3624_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3624_pb : Scalar.QComplex := ((-925871990595044068685996 : Int)/10^30,(-431476456361085796747842988 : Int)/10^30)
theorem v3624_pb_checked : Scalar.distance (sourceCoefficient 49 97 1 1) v3624_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3624_pg : Scalar.QComplex := ((-93086207899928777589299 : Int)/10^30,(199746501424693145801 : Int)/10^30)
theorem v3624_pg_checked : Scalar.distance (sourceCoefficient 49 97 1 2) v3624_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3624_mb : Scalar.QComplex := ((-1298216394711996129239078 : Int)/10^30,(-431475496716853488266152026 : Int)/10^30)
theorem v3624_mb_checked : Scalar.distance (sourceCoefficient 49 97 3 1) v3624_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3624_mg : Scalar.QComplex := ((-93086000867444845538123 : Int)/10^30,(280075632020407476118 : Int)/10^30)
theorem v3624_mg_checked : Scalar.distance (sourceCoefficient 49 97 3 2) v3624_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3624_upper : Scalar.QComplex := ((999992504864387997019638722289 : Int)/10^30,(-3871719908121985831322379563 : Int)/10^30)
theorem v3624_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 49 97 5) 1) 14) v3624_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3624 : Material (49 : Basis) (97 : Basis) where
  plus := ![v3624_pa,v3624_pb,v3624_pg]
  minus := ![(Primitive.Addresses.material3624 1).one,v3624_mb,v3624_mg]
  upper := v3624_upper
  lower := (Primitive.Addresses.material3624 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3624_pa_checked.trans (by decide +kernel)
    · exact v3624_pb_checked.trans (by decide +kernel)
    · exact v3624_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 49 97 Primitive.Addresses.material3624
    · exact v3624_mb_checked.trans (by decide +kernel)
    · exact v3624_mg_checked.trans (by decide +kernel)
  upper_error := v3624_upper_checked
  lower_error := reuse_lower_error 49 97 Primitive.Addresses.material3624

def v3625_pa : Scalar.QComplex := ((999999319283824158555239803556 : Int)/10^30,(-1166804134509463189788712187 : Int)/10^30)
theorem v3625_pa_checked : Scalar.distance (sourceCoefficient 50 51 1 0) v3625_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3625_pb : Scalar.QComplex := ((-503449755440742442650090 : Int)/10^30,(-431477227277743280764883237 : Int)/10^30)
theorem v3625_pb_checked : Scalar.distance (sourceCoefficient 50 51 1 1) v3625_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3625_pg : Scalar.QComplex := ((-93086366530547083015029 : Int)/10^30,(108613631269361372895 : Int)/10^30)
theorem v3625_pg_checked : Scalar.distance (sourceCoefficient 50 51 1 2) v3625_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3625_mb : Scalar.QComplex := ((-875794982111152912364881 : Int)/10^30,(-431476632164587671718228415 : Int)/10^30)
theorem v3625_mb_checked : Scalar.distance (sourceCoefficient 50 51 3 1) v3625_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3625_mg : Scalar.QComplex := ((-93086238141566557479572 : Int)/10^30,(188942932689087379711 : Int)/10^30)
theorem v3625_mg_checked : Scalar.distance (sourceCoefficient 50 51 3 2) v3625_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3625_upper : Scalar.QComplex := ((999995816104221737912803908613 : Int)/10^30,(-2892710502546062080250344936 : Int)/10^30)
theorem v3625_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 51 5) 1) 14) v3625_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3625 : Material (50 : Basis) (51 : Basis) where
  plus := ![v3625_pa,v3625_pb,v3625_pg]
  minus := ![(Primitive.Addresses.material3625 1).one,v3625_mb,v3625_mg]
  upper := v3625_upper
  lower := (Primitive.Addresses.material3625 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3625_pa_checked.trans (by decide +kernel)
    · exact v3625_pb_checked.trans (by decide +kernel)
    · exact v3625_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 51 Primitive.Addresses.material3625
    · exact v3625_mb_checked.trans (by decide +kernel)
    · exact v3625_mg_checked.trans (by decide +kernel)
  upper_error := v3625_upper_checked
  lower_error := reuse_lower_error 50 51 Primitive.Addresses.material3625

def v3626_pa : Scalar.QComplex := ((999999290767526144284577487017 : Int)/10^30,(-1190993049812100655622045241 : Int)/10^30)
theorem v3626_pa_checked : Scalar.distance (sourceCoefficient 50 52 1 0) v3626_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3626_pb : Scalar.QComplex := ((-513886728554066260565001 : Int)/10^30,(-431477214892215174837793260 : Int)/10^30)
theorem v3626_pb_checked : Scalar.distance (sourceCoefficient 50 52 1 1) v3626_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3626_pg : Scalar.QComplex := ((-93086363867287592043240 : Int)/10^30,(110865291027484397890 : Int)/10^30)
theorem v3626_pg_checked : Scalar.distance (sourceCoefficient 50 52 1 2) v3626_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3626_mb : Scalar.QComplex := ((-886231940650161715017543 : Int)/10^30,(-431476610772426444510278914 : Int)/10^30)
theorem v3626_mb_checked : Scalar.distance (sourceCoefficient 50 52 3 1) v3626_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3626_mg : Scalar.QComplex := ((-93086233535227097891790 : Int)/10^30,(191194589310541578869 : Int)/10^30)
theorem v3626_mg_checked : Scalar.distance (sourceCoefficient 50 52 3 2) v3626_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3626_upper : Scalar.QComplex := ((999995745840092784220541527960 : Int)/10^30,(-2916899332605608238112488368 : Int)/10^30)
theorem v3626_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 52 5) 1) 14) v3626_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3626 : Material (50 : Basis) (52 : Basis) where
  plus := ![v3626_pa,v3626_pb,v3626_pg]
  minus := ![(Primitive.Addresses.material3626 1).one,v3626_mb,v3626_mg]
  upper := v3626_upper
  lower := (Primitive.Addresses.material3626 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3626_pa_checked.trans (by decide +kernel)
    · exact v3626_pb_checked.trans (by decide +kernel)
    · exact v3626_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 52 Primitive.Addresses.material3626
    · exact v3626_mb_checked.trans (by decide +kernel)
    · exact v3626_mg_checked.trans (by decide +kernel)
  upper_error := v3626_upper_checked
  lower_error := reuse_lower_error 50 52 Primitive.Addresses.material3626

def v3627_pa : Scalar.QComplex := ((999999286350793282962644341423 : Int)/10^30,(-1194695737055625583293323857 : Int)/10^30)
theorem v3627_pa_checked : Scalar.distance (sourceCoefficient 50 53 1 0) v3627_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3627_pb : Scalar.QComplex := ((-515484354842851404275189 : Int)/10^30,(-431477212966609358531129567 : Int)/10^30)
theorem v3627_pb_checked : Scalar.distance (sourceCoefficient 50 53 1 1) v3627_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3627_pg : Scalar.QComplex := ((-93086363454004729449767 : Int)/10^30,(111209960961410448259 : Int)/10^30)
theorem v3627_pg_checked : Scalar.distance (sourceCoefficient 50 53 1 2) v3627_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3627_mb : Scalar.QComplex := ((-887829564682366482878497 : Int)/10^30,(-431476607468141812390059514 : Int)/10^30)
theorem v3627_mb_checked : Scalar.distance (sourceCoefficient 50 53 3 1) v3627_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3627_mg : Scalar.QComplex := ((-93086232824509759561803 : Int)/10^30,(191539258759486763793 : Int)/10^30)
theorem v3627_mg_checked : Scalar.distance (sourceCoefficient 50 53 3 2) v3627_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3627_upper : Scalar.QComplex := ((999995735032864223942139721091 : Int)/10^30,(-2920602006711535228984015731 : Int)/10^30)
theorem v3627_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 53 5) 1) 14) v3627_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3627 : Material (50 : Basis) (53 : Basis) where
  plus := ![v3627_pa,v3627_pb,v3627_pg]
  minus := ![(Primitive.Addresses.material3627 1).one,v3627_mb,v3627_mg]
  upper := v3627_upper
  lower := (Primitive.Addresses.material3627 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3627_pa_checked.trans (by decide +kernel)
    · exact v3627_pb_checked.trans (by decide +kernel)
    · exact v3627_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 53 Primitive.Addresses.material3627
    · exact v3627_mb_checked.trans (by decide +kernel)
    · exact v3627_mg_checked.trans (by decide +kernel)
  upper_error := v3627_upper_checked
  lower_error := reuse_lower_error 50 53 Primitive.Addresses.material3627

def v3628_pa : Scalar.QComplex := ((999999284100042551425231442319 : Int)/10^30,(-1196578205711770626282458950 : Int)/10^30)
theorem v3628_pa_checked : Scalar.distance (sourceCoefficient 50 54 1 0) v3628_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3628_pb : Scalar.QComplex := ((-516296597738756736262550 : Int)/10^30,(-431477211984595339375911400 : Int)/10^30)
theorem v3628_pb_checked : Scalar.distance (sourceCoefficient 50 54 1 1) v3628_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3628_pg : Scalar.QComplex := ((-93086363243318305793669 : Int)/10^30,(111385193246579041281 : Int)/10^30)
theorem v3628_pg_checked : Scalar.distance (sourceCoefficient 50 54 1 2) v3628_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3628_mb : Scalar.QComplex := ((-888641806428402793124768 : Int)/10^30,(-431476605785199121779281031 : Int)/10^30)
theorem v3628_mb_checked : Scalar.distance (sourceCoefficient 50 54 3 1) v3628_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3628_mg : Scalar.QComplex := ((-93086232462605844422547 : Int)/10^30,(191714490797595473886 : Int)/10^30)
theorem v3628_mg_checked : Scalar.distance (sourceCoefficient 50 54 3 2) v3628_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3628_upper : Scalar.QComplex := ((999995729533146720349660332221 : Int)/10^30,(-2922484468679372762824789490 : Int)/10^30)
theorem v3628_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 54 5) 1) 14) v3628_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3628 : Material (50 : Basis) (54 : Basis) where
  plus := ![v3628_pa,v3628_pb,v3628_pg]
  minus := ![(Primitive.Addresses.material3628 1).one,v3628_mb,v3628_mg]
  upper := v3628_upper
  lower := (Primitive.Addresses.material3628 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3628_pa_checked.trans (by decide +kernel)
    · exact v3628_pb_checked.trans (by decide +kernel)
    · exact v3628_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 54 Primitive.Addresses.material3628
    · exact v3628_mb_checked.trans (by decide +kernel)
    · exact v3628_mg_checked.trans (by decide +kernel)
  upper_error := v3628_upper_checked
  lower_error := reuse_lower_error 50 54 Primitive.Addresses.material3628

def v3629_pa : Scalar.QComplex := ((999999265622517059840451045959 : Int)/10^30,(-1211921790616057719369921377 : Int)/10^30)
theorem v3629_pa_checked : Scalar.distance (sourceCoefficient 50 55 1 0) v3629_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3629_pb : Scalar.QComplex := ((-522917009584292407593805 : Int)/10^30,(-431477203904387477254957346 : Int)/10^30)
theorem v3629_pb_checked : Scalar.distance (sourceCoefficient 50 55 1 1) v3629_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3629_pg : Scalar.QComplex := ((-93086361511707810282866 : Int)/10^30,(112813472772876783656 : Int)/10^30)
theorem v3629_pg_checked : Scalar.distance (sourceCoefficient 50 55 1 2) v3629_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3629_mb : Scalar.QComplex := ((-895262208836001100637017 : Int)/10^30,(-431476591991877017872561002 : Int)/10^30)
theorem v3629_mb_checked : Scalar.distance (sourceCoefficient 50 55 3 1) v3629_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3629_mg : Scalar.QComplex := ((-93086229498455089796440 : Int)/10^30,(193142768297777604236 : Int)/10^30)
theorem v3629_mg_checked : Scalar.distance (sourceCoefficient 50 55 3 2) v3629_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3629_upper : Scalar.QComplex := ((999995684574013163218183133432 : Int)/10^30,(-2937827998840659794613039801 : Int)/10^30)
theorem v3629_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 55 5) 1) 14) v3629_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3629 : Material (50 : Basis) (55 : Basis) where
  plus := ![v3629_pa,v3629_pb,v3629_pg]
  minus := ![(Primitive.Addresses.material3629 1).one,v3629_mb,v3629_mg]
  upper := v3629_upper
  lower := (Primitive.Addresses.material3629 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3629_pa_checked.trans (by decide +kernel)
    · exact v3629_pb_checked.trans (by decide +kernel)
    · exact v3629_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 55 Primitive.Addresses.material3629
    · exact v3629_mb_checked.trans (by decide +kernel)
    · exact v3629_mg_checked.trans (by decide +kernel)
  upper_error := v3629_upper_checked
  lower_error := reuse_lower_error 50 55 Primitive.Addresses.material3629

def v3630_pa : Scalar.QComplex := ((999999261202717455015092218382 : Int)/10^30,(-1215563251858390592285246513 : Int)/10^30)
theorem v3630_pa_checked : Scalar.distance (sourceCoefficient 50 56 1 0) v3630_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3630_pb : Scalar.QComplex := ((-524488218216044521749079 : Int)/10^30,(-431477201966842123561726090 : Int)/10^30)
theorem v3630_pb_checked : Scalar.distance (sourceCoefficient 50 56 1 1) v3630_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3630_pg : Scalar.QComplex := ((-93086361096994301039402 : Int)/10^30,(113152443395444469415 : Int)/10^30)
theorem v3630_pg_checked : Scalar.distance (sourceCoefficient 50 56 1 2) v3630_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3630_mb : Scalar.QComplex := ((-896833415210706056975218 : Int)/10^30,(-431476588698450101023808926 : Int)/10^30)
theorem v3630_mb_checked : Scalar.distance (sourceCoefficient 50 56 3 1) v3630_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3630_mg : Scalar.QComplex := ((-93086228791225354363972 : Int)/10^30,(193481738436251955017 : Int)/10^30)
theorem v3630_mg_checked : Scalar.distance (sourceCoefficient 50 56 3 2) v3630_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3630_upper : Scalar.QComplex := ((999995673869388387681956644601 : Int)/10^30,(-2941469447031290746318745586 : Int)/10^30)
theorem v3630_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 56 5) 1) 14) v3630_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3630 : Material (50 : Basis) (56 : Basis) where
  plus := ![v3630_pa,v3630_pb,v3630_pg]
  minus := ![(Primitive.Addresses.material3630 1).one,v3630_mb,v3630_mg]
  upper := v3630_upper
  lower := (Primitive.Addresses.material3630 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3630_pa_checked.trans (by decide +kernel)
    · exact v3630_pb_checked.trans (by decide +kernel)
    · exact v3630_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 56 Primitive.Addresses.material3630
    · exact v3630_mb_checked.trans (by decide +kernel)
    · exact v3630_mg_checked.trans (by decide +kernel)
  upper_error := v3630_upper_checked
  lower_error := reuse_lower_error 50 56 Primitive.Addresses.material3630

def v3631_pa : Scalar.QComplex := ((999999246816629186650391148266 : Int)/10^30,(-1227341099426524194298917820 : Int)/10^30)
theorem v3631_pa_checked : Scalar.distance (sourceCoefficient 50 57 1 0) v3631_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3631_pb : Scalar.QComplex := ((-529570094547302399656568 : Int)/10^30,(-431477195647856361194855304 : Int)/10^30)
theorem v3631_pb_checked : Scalar.distance (sourceCoefficient 50 57 1 1) v3631_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3631_pg : Scalar.QComplex := ((-93086359745794392886250 : Int)/10^30,(114248801162313406199 : Int)/10^30)
theorem v3631_pg_checked : Scalar.distance (sourceCoefficient 50 57 1 2) v3631_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3631_mb : Scalar.QComplex := ((-901915284196749007164926 : Int)/10^30,(-431476577994036296842144821 : Int)/10^30)
theorem v3631_mb_checked : Scalar.distance (sourceCoefficient 50 57 3 1) v3631_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3631_mg : Scalar.QComplex := ((-93086226493918574637223 : Int)/10^30,(194578094628872124219 : Int)/10^30)
theorem v3631_mg_checked : Scalar.distance (sourceCoefficient 50 57 3 2) v3631_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3631_upper : Scalar.QComplex := ((999995639155825121092114694973 : Int)/10^30,(-2953247252228620663295354712 : Int)/10^30)
theorem v3631_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 57 5) 1) 14) v3631_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3631 : Material (50 : Basis) (57 : Basis) where
  plus := ![v3631_pa,v3631_pb,v3631_pg]
  minus := ![(Primitive.Addresses.material3631 1).one,v3631_mb,v3631_mg]
  upper := v3631_upper
  lower := (Primitive.Addresses.material3631 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3631_pa_checked.trans (by decide +kernel)
    · exact v3631_pb_checked.trans (by decide +kernel)
    · exact v3631_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 57 Primitive.Addresses.material3631
    · exact v3631_mb_checked.trans (by decide +kernel)
    · exact v3631_mg_checked.trans (by decide +kernel)
  upper_error := v3631_upper_checked
  lower_error := reuse_lower_error 50 57 Primitive.Addresses.material3631

def v3632_pa : Scalar.QComplex := ((999999238952824616494982937326 : Int)/10^30,(-1233731644878336933595920533 : Int)/10^30)
theorem v3632_pa_checked : Scalar.distance (sourceCoefficient 50 58 1 0) v3632_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3632_pb : Scalar.QComplex := ((-532327471169238610319080 : Int)/10^30,(-431477192185838060602380438 : Int)/10^30)
theorem v3632_pb_checked : Scalar.distance (sourceCoefficient 50 58 1 1) v3632_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3632_pg : Scalar.QComplex := ((-93086359006341860651453 : Int)/10^30,(114843674214083408588 : Int)/10^30)
theorem v3632_pg_checked : Scalar.distance (sourceCoefficient 50 58 1 2) v3632_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3632_mb : Scalar.QComplex := ((-904672656804422013248332 : Int)/10^30,(-431476572152527448219345889 : Int)/10^30)
theorem v3632_mb_checked : Scalar.distance (sourceCoefficient 50 58 3 1) v3632_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3632_mg : Scalar.QComplex := ((-93086225241117666144569 : Int)/10^30,(195172966821029470780 : Int)/10^30)
theorem v3632_mg_checked : Scalar.distance (sourceCoefficient 50 58 3 2) v3632_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3632_upper : Scalar.QComplex := ((999995620262530559075741474803 : Int)/10^30,(-2959637774590253349008486201 : Int)/10^30)
theorem v3632_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 58 5) 1) 14) v3632_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3632 : Material (50 : Basis) (58 : Basis) where
  plus := ![v3632_pa,v3632_pb,v3632_pg]
  minus := ![(Primitive.Addresses.material3632 1).one,v3632_mb,v3632_mg]
  upper := v3632_upper
  lower := (Primitive.Addresses.material3632 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3632_pa_checked.trans (by decide +kernel)
    · exact v3632_pb_checked.trans (by decide +kernel)
    · exact v3632_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 58 Primitive.Addresses.material3632
    · exact v3632_mb_checked.trans (by decide +kernel)
    · exact v3632_mg_checked.trans (by decide +kernel)
  upper_error := v3632_upper_checked
  lower_error := reuse_lower_error 50 58 Primitive.Addresses.material3632

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
