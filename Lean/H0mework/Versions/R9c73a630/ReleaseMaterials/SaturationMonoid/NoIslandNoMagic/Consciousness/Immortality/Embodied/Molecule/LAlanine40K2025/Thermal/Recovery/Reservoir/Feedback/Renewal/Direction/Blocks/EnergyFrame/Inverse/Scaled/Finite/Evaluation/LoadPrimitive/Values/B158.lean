import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B105
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B106

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2529_pa : Scalar.QComplex := ((999998852023900836857079686953 : Int)/10^30,(-1515239545575933545038335071 : Int)/10^30)
theorem v2529_pa_checked : Scalar.distance (sourceCoefficient 30 85 1 0) v2529_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2529_pb : Scalar.QComplex := ((-653791704391025809213644 : Int)/10^30,(-431476960697506928915517191 : Int)/10^30)
theorem v2529_pb_checked : Scalar.distance (sourceCoefficient 30 85 1 1) v2529_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2529_pg : Scalar.QComplex := ((-93086316026921774118004 : Int)/10^30,(141048229115966543166 : Int)/10^30)
theorem v2529_pg_checked : Scalar.distance (sourceCoefficient 30 85 1 2) v2529_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2529_mb : Scalar.QComplex := ((-1026136645035520074741712 : Int)/10^30,(-431476235846119785803446233 : Int)/10^30)
theorem v2529_mb_checked : Scalar.distance (sourceCoefficient 30 85 3 1) v2529_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2529_mg : Scalar.QComplex := ((-93086159648362911829680 : Int)/10^30,(221377474876455394609 : Int)/10^30)
theorem v2529_mg_checked : Scalar.distance (sourceCoefficient 30 85 3 2) v2529_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2529_upper : Scalar.QComplex := ((999994747477084657824029304915 : Int)/10^30,(-3241144588210679586423051775 : Int)/10^30)
theorem v2529_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 85 5) 1) 14) v2529_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2529 : Material (30 : Basis) (85 : Basis) where
  plus := ![v2529_pa,v2529_pb,v2529_pg]
  minus := ![(Primitive.Addresses.material2529 1).one,v2529_mb,v2529_mg]
  upper := v2529_upper
  lower := (Primitive.Addresses.material2529 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2529_pa_checked.trans (by decide +kernel)
    · exact v2529_pb_checked.trans (by decide +kernel)
    · exact v2529_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 85 Primitive.Addresses.material2529
    · exact v2529_mb_checked.trans (by decide +kernel)
    · exact v2529_mg_checked.trans (by decide +kernel)
  upper_error := v2529_upper_checked
  lower_error := reuse_lower_error 30 85 Primitive.Addresses.material2529

def v2530_pa : Scalar.QComplex := ((999998829818315538583122141350 : Int)/10^30,(-1529824172772040854562414866 : Int)/10^30)
theorem v2530_pa_checked : Scalar.distance (sourceCoefficient 30 86 1 0) v2530_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2530_pb : Scalar.QComplex := ((-660084639156884766325961 : Int)/10^30,(-431476949107071631564861999 : Int)/10^30)
theorem v2530_pb_checked : Scalar.distance (sourceCoefficient 30 86 1 1) v2530_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2530_pg : Scalar.QComplex := ((-93086313743149309366689 : Int)/10^30,(142405859559240666293 : Int)/10^30)
theorem v2530_pg_checked : Scalar.distance (sourceCoefficient 30 86 1 2) v2530_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2530_mb : Scalar.QComplex := ((-1032429567456208169412258 : Int)/10^30,(-431476218825169524425969616 : Int)/10^30)
theorem v2530_mb_checked : Scalar.distance (sourceCoefficient 30 86 3 1) v2530_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2530_mg : Scalar.QComplex := ((-93086156193017370291001 : Int)/10^30,(222735102843428877142 : Int)/10^30)
theorem v2530_mg_checked : Scalar.distance (sourceCoefficient 30 86 3 2) v2530_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2530_upper : Scalar.QComplex := ((999994700099788998723391844896 : Int)/10^30,(-3255729155359872168144832459 : Int)/10^30)
theorem v2530_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 86 5) 1) 14) v2530_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2530 : Material (30 : Basis) (86 : Basis) where
  plus := ![v2530_pa,v2530_pb,v2530_pg]
  minus := ![(Primitive.Addresses.material2530 1).one,v2530_mb,v2530_mg]
  upper := v2530_upper
  lower := (Primitive.Addresses.material2530 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2530_pa_checked.trans (by decide +kernel)
    · exact v2530_pb_checked.trans (by decide +kernel)
    · exact v2530_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 86 Primitive.Addresses.material2530
    · exact v2530_mb_checked.trans (by decide +kernel)
    · exact v2530_mg_checked.trans (by decide +kernel)
  upper_error := v2530_upper_checked
  lower_error := reuse_lower_error 30 86 Primitive.Addresses.material2530

def v2531_pa : Scalar.QComplex := ((999998828340411648819709945876 : Int)/10^30,(-1530789928081632501061351399 : Int)/10^30)
theorem v2531_pa_checked : Scalar.distance (sourceCoefficient 30 87 1 0) v2531_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2531_pb : Scalar.QComplex := ((-660501340593749620873455 : Int)/10^30,(-431476948335263839647577773 : Int)/10^30)
theorem v2531_pb_checked : Scalar.distance (sourceCoefficient 30 87 1 1) v2531_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2531_pg : Scalar.QComplex := ((-93086313591108478575928 : Int)/10^30,(142495758244038683952 : Int)/10^30)
theorem v2531_pg_checked : Scalar.distance (sourceCoefficient 30 87 1 2) v2531_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2531_mb : Scalar.QComplex := ((-1032846268071880671326445 : Int)/10^30,(-431476217693767447409662912 : Int)/10^30)
theorem v2531_mb_checked : Scalar.distance (sourceCoefficient 30 87 3 1) v2531_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2531_mg : Scalar.QComplex := ((-93086155963398080017762 : Int)/10^30,(222825001363549116570 : Int)/10^30)
theorem v2531_mg_checked : Scalar.distance (sourceCoefficient 30 87 3 2) v2531_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2531_upper : Scalar.QComplex := ((999994696955081258406328598740 : Int)/10^30,(-3256694906680356687256692262 : Int)/10^30)
theorem v2531_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 87 5) 1) 14) v2531_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2531 : Material (30 : Basis) (87 : Basis) where
  plus := ![v2531_pa,v2531_pb,v2531_pg]
  minus := ![(Primitive.Addresses.material2531 1).one,v2531_mb,v2531_mg]
  upper := v2531_upper
  lower := (Primitive.Addresses.material2531 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2531_pa_checked.trans (by decide +kernel)
    · exact v2531_pb_checked.trans (by decide +kernel)
    · exact v2531_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 87 Primitive.Addresses.material2531
    · exact v2531_mb_checked.trans (by decide +kernel)
    · exact v2531_mg_checked.trans (by decide +kernel)
  upper_error := v2531_upper_checked
  lower_error := reuse_lower_error 30 87 Primitive.Addresses.material2531

def v2532_pa : Scalar.QComplex := ((999998810269800336948307420382 : Int)/10^30,(-1542549507752718902949221155 : Int)/10^30)
theorem v2532_pa_checked : Scalar.distance (sourceCoefficient 30 88 1 0) v2532_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2532_pb : Scalar.QComplex := ((-665575331553051382532500 : Int)/10^30,(-431476938894252575211823803 : Int)/10^30)
theorem v2532_pb_checked : Scalar.distance (sourceCoefficient 30 88 1 1) v2532_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2532_pg : Scalar.QComplex := ((-93086311731648046673999 : Int)/10^30,(143590415174023151832 : Int)/10^30)
theorem v2532_pg_checked : Scalar.distance (sourceCoefficient 30 88 1 2) v2532_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2532_mb : Scalar.QComplex := ((-1037920248994736192149720 : Int)/10^30,(-431476203874134024486052642 : Int)/10^30)
theorem v2532_mb_checked : Scalar.distance (sourceCoefficient 30 88 3 1) v2532_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2532_mg : Scalar.QComplex := ((-93086153159298711419305 : Int)/10^30,(223919656281312175381 : Int)/10^30)
theorem v2532_mg_checked : Scalar.distance (sourceCoefficient 30 88 3 2) v2532_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2532_upper : Scalar.QComplex := ((999994658588529169026837043683 : Int)/10^30,(-3268454437648694775088241481 : Int)/10^30)
theorem v2532_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 88 5) 1) 14) v2532_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2532 : Material (30 : Basis) (88 : Basis) where
  plus := ![v2532_pa,v2532_pb,v2532_pg]
  minus := ![(Primitive.Addresses.material2532 1).one,v2532_mb,v2532_mg]
  upper := v2532_upper
  lower := (Primitive.Addresses.material2532 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2532_pa_checked.trans (by decide +kernel)
    · exact v2532_pb_checked.trans (by decide +kernel)
    · exact v2532_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 88 Primitive.Addresses.material2532
    · exact v2532_mb_checked.trans (by decide +kernel)
    · exact v2532_mg_checked.trans (by decide +kernel)
  upper_error := v2532_upper_checked
  lower_error := reuse_lower_error 30 88 Primitive.Addresses.material2532

def v2533_pa : Scalar.QComplex := ((999998785321538298113433540763 : Int)/10^30,(-1558638972937610016842903536 : Int)/10^30)
theorem v2533_pa_checked : Scalar.distance (sourceCoefficient 30 89 1 0) v2533_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2533_pb : Scalar.QComplex := ((-672517569442866562422770 : Int)/10^30,(-431476925848164122742156774 : Int)/10^30)
theorem v2533_pb_checked : Scalar.distance (sourceCoefficient 30 89 1 1) v2533_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2533_pg : Scalar.QComplex := ((-93086309163202176770053 : Int)/10^30,(145088125544107424058 : Int)/10^30)
theorem v2533_pg_checked : Scalar.distance (sourceCoefficient 30 89 1 2) v2533_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2533_mb : Scalar.QComplex := ((-1044862473041452169247288 : Int)/10^30,(-431476184837211797548672452 : Int)/10^30)
theorem v2533_mb_checked : Scalar.distance (sourceCoefficient 30 89 3 1) v2533_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2533_mg : Scalar.QComplex := ((-93086149298397202853458 : Int)/10^30,(225417363877277320861 : Int)/10^30)
theorem v2533_mg_checked : Scalar.distance (sourceCoefficient 30 89 3 2) v2533_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2533_upper : Scalar.QComplex := ((999994605871347003455188187367 : Int)/10^30,(-3284543835811780507055910435 : Int)/10^30)
theorem v2533_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 89 5) 1) 14) v2533_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2533 : Material (30 : Basis) (89 : Basis) where
  plus := ![v2533_pa,v2533_pb,v2533_pg]
  minus := ![(Primitive.Addresses.material2533 1).one,v2533_mb,v2533_mg]
  upper := v2533_upper
  lower := (Primitive.Addresses.material2533 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2533_pa_checked.trans (by decide +kernel)
    · exact v2533_pb_checked.trans (by decide +kernel)
    · exact v2533_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 89 Primitive.Addresses.material2533
    · exact v2533_mb_checked.trans (by decide +kernel)
    · exact v2533_mg_checked.trans (by decide +kernel)
  upper_error := v2533_upper_checked
  lower_error := reuse_lower_error 30 89 Primitive.Addresses.material2533

def v2534_pa : Scalar.QComplex := ((999998744137315533060484704063 : Int)/10^30,(-1584841882252862723759167998 : Int)/10^30)
theorem v2534_pa_checked : Scalar.distance (sourceCoefficient 30 90 1 0) v2534_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2534_pb : Scalar.QComplex := ((-683823527920725125142428 : Int)/10^30,(-431476904282852126008662747 : Int)/10^30)
theorem v2534_pb_checked : Scalar.distance (sourceCoefficient 30 90 1 1) v2534_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2534_pg : Scalar.QComplex := ((-93086304920119085839076 : Int)/10^30,(147527259975546193214 : Int)/10^30)
theorem v2534_pg_checked : Scalar.distance (sourceCoefficient 30 90 1 2) v2534_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2534_mb : Scalar.QComplex := ((-1056168408699692695248134 : Int)/10^30,(-431476153515374865641874391 : Int)/10^30)
theorem v2534_mb_checked : Scalar.distance (sourceCoefficient 30 90 3 1) v2534_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2534_mg : Scalar.QComplex := ((-93086142950452532021376 : Int)/10^30,(227856493738925261136 : Int)/10^30)
theorem v2534_mg_checked : Scalar.distance (sourceCoefficient 30 90 3 2) v2534_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2534_upper : Scalar.QComplex := ((999994519463341208702157521626 : Int)/10^30,(-3310746635020645509872079202 : Int)/10^30)
theorem v2534_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 90 5) 1) 14) v2534_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2534 : Material (30 : Basis) (90 : Basis) where
  plus := ![v2534_pa,v2534_pb,v2534_pg]
  minus := ![(Primitive.Addresses.material2534 1).one,v2534_mb,v2534_mg]
  upper := v2534_upper
  lower := (Primitive.Addresses.material2534 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2534_pa_checked.trans (by decide +kernel)
    · exact v2534_pb_checked.trans (by decide +kernel)
    · exact v2534_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 90 Primitive.Addresses.material2534
    · exact v2534_mb_checked.trans (by decide +kernel)
    · exact v2534_mg_checked.trans (by decide +kernel)
  upper_error := v2534_upper_checked
  lower_error := reuse_lower_error 30 90 Primitive.Addresses.material2534

def v2535_pa : Scalar.QComplex := ((999998720634407533887305207361 : Int)/10^30,(-1599602934529662021468005227 : Int)/10^30)
theorem v2535_pa_checked : Scalar.distance (sourceCoefficient 30 91 1 0) v2535_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2535_pb : Scalar.QComplex := ((-690192585570227212417726 : Int)/10^30,(-431476891960392050539544334 : Int)/10^30)
theorem v2535_pb_checked : Scalar.distance (sourceCoefficient 30 91 1 1) v2535_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2535_pg : Scalar.QComplex := ((-93086302497001987463020 : Int)/10^30,(148901313137936886200 : Int)/10^30)
theorem v2535_pg_checked : Scalar.distance (sourceCoefficient 30 91 1 2) v2535_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2535_mb : Scalar.QComplex := ((-1062537453343975477169577 : Int)/10^30,(-431476135696709478575602638 : Int)/10^30)
theorem v2535_mb_checked : Scalar.distance (sourceCoefficient 30 91 3 1) v2535_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2535_mg : Scalar.QComplex := ((-93086139341590341796543 : Int)/10^30,(229230544298652241677 : Int)/10^30)
theorem v2535_mg_checked : Scalar.distance (sourceCoefficient 30 91 3 2) v2535_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2535_upper : Scalar.QComplex := ((999994470484231096795990205212 : Int)/10^30,(-3325507624748704356877692397 : Int)/10^30)
theorem v2535_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 91 5) 1) 14) v2535_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2535 : Material (30 : Basis) (91 : Basis) where
  plus := ![v2535_pa,v2535_pb,v2535_pg]
  minus := ![(Primitive.Addresses.material2535 1).one,v2535_mb,v2535_mg]
  upper := v2535_upper
  lower := (Primitive.Addresses.material2535 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2535_pa_checked.trans (by decide +kernel)
    · exact v2535_pb_checked.trans (by decide +kernel)
    · exact v2535_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 91 Primitive.Addresses.material2535
    · exact v2535_mb_checked.trans (by decide +kernel)
    · exact v2535_mg_checked.trans (by decide +kernel)
  upper_error := v2535_upper_checked
  lower_error := reuse_lower_error 30 91 Primitive.Addresses.material2535

def v2536_pa : Scalar.QComplex := ((999998669006733127662950600280 : Int)/10^30,(-1631558997462732770578778140 : Int)/10^30)
theorem v2536_pa_checked : Scalar.distance (sourceCoefficient 30 92 1 0) v2536_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2536_pb : Scalar.QComplex := ((-703980898043683441068076 : Int)/10^30,(-431476864854179498033562926 : Int)/10^30)
theorem v2536_pb_checked : Scalar.distance (sourceCoefficient 30 92 1 1) v2536_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2536_pg : Scalar.QComplex := ((-93086297170153540891961 : Int)/10^30,(151875987834370936839 : Int)/10^30)
theorem v2536_pg_checked : Scalar.distance (sourceCoefficient 30 92 1 2) v2536_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2536_mb : Scalar.QComplex := ((-1076325737291972200623538 : Int)/10^30,(-431476096691814356899750856 : Int)/10^30)
theorem v2536_mb_checked : Scalar.distance (sourceCoefficient 30 92 3 1) v2536_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2536_mg : Scalar.QComplex := ((-93086131447733590006989 : Int)/10^30,(232205213290648656441 : Int)/10^30)
theorem v2536_mg_checked : Scalar.distance (sourceCoefficient 30 92 3 2) v2536_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2536_upper : Scalar.QComplex := ((999994363703367992831235840111 : Int)/10^30,(-3357463550982290790915793478 : Int)/10^30)
theorem v2536_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 92 5) 1) 14) v2536_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2536 : Material (30 : Basis) (92 : Basis) where
  plus := ![v2536_pa,v2536_pb,v2536_pg]
  minus := ![(Primitive.Addresses.material2536 1).one,v2536_mb,v2536_mg]
  upper := v2536_upper
  lower := (Primitive.Addresses.material2536 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2536_pa_checked.trans (by decide +kernel)
    · exact v2536_pb_checked.trans (by decide +kernel)
    · exact v2536_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 92 Primitive.Addresses.material2536
    · exact v2536_mb_checked.trans (by decide +kernel)
    · exact v2536_mg_checked.trans (by decide +kernel)
  upper_error := v2536_upper_checked
  lower_error := reuse_lower_error 30 92 Primitive.Addresses.material2536

def v2537_pa : Scalar.QComplex := ((999998606409685084988234094455 : Int)/10^30,(-1669484557501523494367339548 : Int)/10^30)
theorem v2537_pa_checked : Scalar.distance (sourceCoefficient 30 93 1 0) v2537_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2537_pb : Scalar.QComplex := ((-720344911679272849628573 : Int)/10^30,(-431476831922072560147843342 : Int)/10^30)
theorem v2537_pb_checked : Scalar.distance (sourceCoefficient 30 93 1 1) v2537_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2537_pg : Scalar.QComplex := ((-93086290704319528470513 : Int)/10^30,(155406341418731345286 : Int)/10^30)
theorem v2537_pg_checked : Scalar.distance (sourceCoefficient 30 93 1 2) v2537_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2537_mb : Scalar.QComplex := ((-1092689716415566379927180 : Int)/10^30,(-431476049638312921443987126 : Int)/10^30)
theorem v2537_mb_checked : Scalar.distance (sourceCoefficient 30 93 3 1) v2537_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2537_mg : Scalar.QComplex := ((-93086121935365843031051 : Int)/10^30,(235735559980773537936 : Int)/10^30)
theorem v2537_mg_checked : Scalar.distance (sourceCoefficient 30 93 3 2) v2537_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2537_upper : Scalar.QComplex := ((999994235650337134084007452760 : Int)/10^30,(-3395388946498588724339701276 : Int)/10^30)
theorem v2537_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 93 5) 1) 14) v2537_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2537 : Material (30 : Basis) (93 : Basis) where
  plus := ![v2537_pa,v2537_pb,v2537_pg]
  minus := ![(Primitive.Addresses.material2537 1).one,v2537_mb,v2537_mg]
  upper := v2537_upper
  lower := (Primitive.Addresses.material2537 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2537_pa_checked.trans (by decide +kernel)
    · exact v2537_pb_checked.trans (by decide +kernel)
    · exact v2537_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 93 Primitive.Addresses.material2537
    · exact v2537_mb_checked.trans (by decide +kernel)
    · exact v2537_mg_checked.trans (by decide +kernel)
  upper_error := v2537_upper_checked
  lower_error := reuse_lower_error 30 93 Primitive.Addresses.material2537

def v2538_pa : Scalar.QComplex := ((999998530615731192381326660177 : Int)/10^30,(-1714283050877277946197349858 : Int)/10^30)
theorem v2538_pa_checked : Scalar.distance (sourceCoefficient 30 94 1 0) v2538_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2538_pb : Scalar.QComplex := ((-739674438162951351427697 : Int)/10^30,(-431476791955939132568769957 : Int)/10^30)
theorem v2538_pb_checked : Scalar.distance (sourceCoefficient 30 94 1 1) v2538_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2538_pg : Scalar.QComplex := ((-93086282865502970268616 : Int)/10^30,(159576471464656556702 : Int)/10^30)
theorem v2538_pg_checked : Scalar.distance (sourceCoefficient 30 94 1 2) v2538_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2538_mb : Scalar.QComplex := ((-1112019201213005628680907 : Int)/10^30,(-431475992991683589224148199 : Int)/10^30)
theorem v2538_mb_checked : Scalar.distance (sourceCoefficient 30 94 3 1) v2538_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2538_mg : Scalar.QComplex := ((-93086110497917789630575 : Int)/10^30,(239905681709423106359 : Int)/10^30)
theorem v2538_mg_checked : Scalar.distance (sourceCoefficient 30 94 3 2) v2538_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2538_upper : Scalar.QComplex := ((999994082538360648687994494751 : Int)/10^30,(-3440187242338761248824314056 : Int)/10^30)
theorem v2538_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 94 5) 1) 14) v2538_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2538 : Material (30 : Basis) (94 : Basis) where
  plus := ![v2538_pa,v2538_pb,v2538_pg]
  minus := ![(Primitive.Addresses.material2538 1).one,v2538_mb,v2538_mg]
  upper := v2538_upper
  lower := (Primitive.Addresses.material2538 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2538_pa_checked.trans (by decide +kernel)
    · exact v2538_pb_checked.trans (by decide +kernel)
    · exact v2538_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 94 Primitive.Addresses.material2538
    · exact v2538_mb_checked.trans (by decide +kernel)
    · exact v2538_mg_checked.trans (by decide +kernel)
  upper_error := v2538_upper_checked
  lower_error := reuse_lower_error 30 94 Primitive.Addresses.material2538

def v2539_pa : Scalar.QComplex := ((999998453737077981453069331668 : Int)/10^30,(-1758557207800778328720150395 : Int)/10^30)
theorem v2539_pa_checked : Scalar.distance (sourceCoefficient 30 95 1 0) v2539_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2539_pb : Scalar.QComplex := ((-758777724307723380254255 : Int)/10^30,(-431476751323191385837180381 : Int)/10^30)
theorem v2539_pb_checked : Scalar.distance (sourceCoefficient 30 95 1 1) v2539_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2539_pg : Scalar.QComplex := ((-93086274904293738265179 : Int)/10^30,(163697792800097883382 : Int)/10^30)
theorem v2539_pg_checked : Scalar.distance (sourceCoefficient 30 95 1 2) v2539_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2539_mb : Scalar.QComplex := ((-1131122445180519888097026 : Int)/10^30,(-431475935873675409052443233 : Int)/10^30)
theorem v2539_mb_checked : Scalar.distance (sourceCoefficient 30 95 3 1) v2539_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2539_mg : Scalar.QComplex := ((-93086098980196826885821 : Int)/10^30,(244026994640143138499 : Int)/10^30)
theorem v2539_mg_checked : Scalar.distance (sourceCoefficient 30 95 3 2) v2539_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2539_upper : Scalar.QComplex := ((999993929246643609662000067065 : Int)/10^30,(-3484461200635524636478632193 : Int)/10^30)
theorem v2539_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 95 5) 1) 14) v2539_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2539 : Material (30 : Basis) (95 : Basis) where
  plus := ![v2539_pa,v2539_pb,v2539_pg]
  minus := ![(Primitive.Addresses.material2539 1).one,v2539_mb,v2539_mg]
  upper := v2539_upper
  lower := (Primitive.Addresses.material2539 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2539_pa_checked.trans (by decide +kernel)
    · exact v2539_pb_checked.trans (by decide +kernel)
    · exact v2539_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 95 Primitive.Addresses.material2539
    · exact v2539_mb_checked.trans (by decide +kernel)
    · exact v2539_mg_checked.trans (by decide +kernel)
  upper_error := v2539_upper_checked
  lower_error := reuse_lower_error 30 95 Primitive.Addresses.material2539

def v2540_pa : Scalar.QComplex := ((999998416116867001381937620965 : Int)/10^30,(-1779821271170635584625204465 : Int)/10^30)
theorem v2540_pa_checked : Scalar.distance (sourceCoefficient 30 96 1 0) v2540_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2540_pb : Scalar.QComplex := ((-767952680920931282837327 : Int)/10^30,(-431476731407154728172024366 : Int)/10^30)
theorem v2540_pb_checked : Scalar.distance (sourceCoefficient 30 96 1 1) v2540_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2540_pg : Scalar.QComplex := ((-93086271004997525400573 : Int)/10^30,(165677187601951938663 : Int)/10^30)
theorem v2540_pg_checked : Scalar.distance (sourceCoefficient 30 96 1 2) v2540_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2540_mb : Scalar.QComplex := ((-1140297381190829476779313 : Int)/10^30,(-431475908040071834545759521 : Int)/10^30)
theorem v2540_mb_checked : Scalar.distance (sourceCoefficient 30 96 3 1) v2540_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2540_mg : Scalar.QComplex := ((-93086093372773500539875 : Int)/10^30,(246006385340061032318 : Int)/10^30)
theorem v2540_mg_checked : Scalar.distance (sourceCoefficient 30 96 3 2) v2540_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2540_upper : Scalar.QComplex := ((999993854926644344862236823996 : Int)/10^30,(-3505725167405986082606676338 : Int)/10^30)
theorem v2540_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 96 5) 1) 14) v2540_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2540 : Material (30 : Basis) (96 : Basis) where
  plus := ![v2540_pa,v2540_pb,v2540_pg]
  minus := ![(Primitive.Addresses.material2540 1).one,v2540_mb,v2540_mg]
  upper := v2540_upper
  lower := (Primitive.Addresses.material2540 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2540_pa_checked.trans (by decide +kernel)
    · exact v2540_pb_checked.trans (by decide +kernel)
    · exact v2540_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 96 Primitive.Addresses.material2540
    · exact v2540_mb_checked.trans (by decide +kernel)
    · exact v2540_mg_checked.trans (by decide +kernel)
  upper_error := v2540_upper_checked
  lower_error := reuse_lower_error 30 96 Primitive.Addresses.material2540

def v2541_pa : Scalar.QComplex := ((999998283224834618370261575844 : Int)/10^30,(-1852983373764128247831363517 : Int)/10^30)
theorem v2541_pa_checked : Scalar.distance (sourceCoefficient 30 97 1 0) v2541_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2541_pb : Scalar.QComplex := ((-799520451404239295944042 : Int)/10^30,(-431476660895910049574602158 : Int)/10^30)
theorem v2541_pb_checked : Scalar.distance (sourceCoefficient 30 97 1 1) v2541_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2541_pg : Scalar.QComplex := ((-93086257213770418060223 : Int)/10^30,(172487583065446673387 : Int)/10^30)
theorem v2541_pg_checked : Scalar.distance (sourceCoefficient 30 97 1 2) v2541_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2541_mb : Scalar.QComplex := ((-1171865079071985371510539 : Int)/10^30,(-431475810287289243016809739 : Int)/10^30)
theorem v2541_mb_checked : Scalar.distance (sourceCoefficient 30 97 3 1) v2541_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2541_mg : Scalar.QComplex := ((-93086073704486972133078 : Int)/10^30,(252816766366526425711 : Int)/10^30)
theorem v2541_mg_checked : Scalar.distance (sourceCoefficient 30 97 3 2) v2541_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2541_upper : Scalar.QComplex := ((999993595763658026654074260181 : Int)/10^30,(-3578886931673529135011811570 : Int)/10^30)
theorem v2541_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 97 5) 1) 14) v2541_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2541 : Material (30 : Basis) (97 : Basis) where
  plus := ![v2541_pa,v2541_pb,v2541_pg]
  minus := ![(Primitive.Addresses.material2541 1).one,v2541_mb,v2541_mg]
  upper := v2541_upper
  lower := (Primitive.Addresses.material2541 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2541_pa_checked.trans (by decide +kernel)
    · exact v2541_pb_checked.trans (by decide +kernel)
    · exact v2541_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 97 Primitive.Addresses.material2541
    · exact v2541_mb_checked.trans (by decide +kernel)
    · exact v2541_mg_checked.trans (by decide +kernel)
  upper_error := v2541_upper_checked
  lower_error := reuse_lower_error 30 97 Primitive.Addresses.material2541

def v2542_pa : Scalar.QComplex := ((999999824974672510602638977851 : Int)/10^30,(-591650762143453559223949122 : Int)/10^30)
theorem v2542_pa_checked : Scalar.distance (sourceCoefficient 31 32 1 0) v2542_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2542_pb : Scalar.QComplex := ((-255284004146833594662059 : Int)/10^30,(-431477445479517849043083084 : Int)/10^30)
theorem v2542_pb_checked : Scalar.distance (sourceCoefficient 31 32 1 1) v2542_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2542_pg : Scalar.QComplex := ((-93086413604316223007255 : Int)/10^30,(55074657193654348864 : Int)/10^30)
theorem v2542_pg_checked : Scalar.distance (sourceCoefficient 31 32 1 2) v2542_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2542_mb : Scalar.QComplex := ((-627629511518999015535697 : Int)/10^30,(-431477064522147389617149922 : Int)/10^30)
theorem v2542_mb_checked : Scalar.distance (sourceCoefficient 31 32 3 1) v2542_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2542_mg : Scalar.QComplex := ((-93086331417041491210843 : Int)/10^30,(135404019170929900012 : Int)/10^30)
theorem v2542_mg_checked : Scalar.distance (sourceCoefficient 31 32 3 2) v2542_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2542_upper : Scalar.QComplex := ((999997314456860120224092360006 : Int)/10^30,(-2317558859579966667983123557 : Int)/10^30)
theorem v2542_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 32 5) 1) 14) v2542_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2542 : Material (31 : Basis) (32 : Basis) where
  plus := ![v2542_pa,v2542_pb,v2542_pg]
  minus := ![(Primitive.Addresses.material2542 1).one,v2542_mb,v2542_mg]
  upper := v2542_upper
  lower := (Primitive.Addresses.material2542 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2542_pa_checked.trans (by decide +kernel)
    · exact v2542_pb_checked.trans (by decide +kernel)
    · exact v2542_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 32 Primitive.Addresses.material2542
    · exact v2542_mb_checked.trans (by decide +kernel)
    · exact v2542_mg_checked.trans (by decide +kernel)
  upper_error := v2542_upper_checked
  lower_error := reuse_lower_error 31 32 Primitive.Addresses.material2542

def v2543_pa : Scalar.QComplex := ((999999821014423519125759096317 : Int)/10^30,(-598306878554736234629039118 : Int)/10^30)
theorem v2543_pa_checked : Scalar.distance (sourceCoefficient 31 33 1 0) v2543_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2543_pb : Scalar.QComplex := ((-258155968750812854486950 : Int)/10^30,(-431477443763001155343069524 : Int)/10^30)
theorem v2543_pb_checked : Scalar.distance (sourceCoefficient 31 33 1 1) v2543_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2543_pg : Scalar.QComplex := ((-93086413234833902398799 : Int)/10^30,(55694251306857436194 : Int)/10^30)
theorem v2543_pg_checked : Scalar.distance (sourceCoefficient 31 33 1 2) v2543_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2543_mb : Scalar.QComplex := ((-630501473572338000411492 : Int)/10^30,(-431477060327255230304770678 : Int)/10^30)
theorem v2543_mb_checked : Scalar.distance (sourceCoefficient 31 33 3 1) v2543_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2543_mg : Scalar.QComplex := ((-93086330512877493966235 : Int)/10^30,(136023612734583180328 : Int)/10^30)
theorem v2543_mg_checked : Scalar.distance (sourceCoefficient 31 33 3 2) v2543_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2543_upper : Scalar.QComplex := ((999997299008763939362890693918 : Int)/10^30,(-2324214959242715342833519004 : Int)/10^30)
theorem v2543_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 33 5) 1) 14) v2543_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2543 : Material (31 : Basis) (33 : Basis) where
  plus := ![v2543_pa,v2543_pb,v2543_pg]
  minus := ![(Primitive.Addresses.material2543 1).one,v2543_mb,v2543_mg]
  upper := v2543_upper
  lower := (Primitive.Addresses.material2543 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2543_pa_checked.trans (by decide +kernel)
    · exact v2543_pb_checked.trans (by decide +kernel)
    · exact v2543_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 33 Primitive.Addresses.material2543
    · exact v2543_mb_checked.trans (by decide +kernel)
    · exact v2543_mg_checked.trans (by decide +kernel)
  upper_error := v2543_upper_checked
  lower_error := reuse_lower_error 31 33 Primitive.Addresses.material2543

def v2544_pa : Scalar.QComplex := ((999999811210931662494368873369 : Int)/10^30,(-614473840805041055825745064 : Int)/10^30)
theorem v2544_pa_checked : Scalar.distance (sourceCoefficient 31 34 1 0) v2544_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2544_pb : Scalar.QComplex := ((-265131649516649713303827 : Int)/10^30,(-431477439487636383054707506 : Int)/10^30)
theorem v2544_pb_checked : Scalar.distance (sourceCoefficient 31 34 1 1) v2544_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2544_pg : Scalar.QComplex := ((-93086412317366903920374 : Int)/10^30,(57199176101993289764 : Int)/10^30)
theorem v2544_pg_checked : Scalar.distance (sourceCoefficient 31 34 1 2) v2544_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2544_mb : Scalar.QComplex := ((-637477148051362862543552 : Int)/10^30,(-431477050032193722011941407 : Int)/10^30)
theorem v2544_mb_checked : Scalar.distance (sourceCoefficient 31 34 3 1) v2544_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2544_mg : Scalar.QComplex := ((-93086328296728518197149 : Int)/10^30,(137528536177634055700 : Int)/10^30)
theorem v2544_mg_checked : Scalar.distance (sourceCoefficient 31 34 3 2) v2544_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2544_upper : Scalar.QComplex := ((999997261302576495213365217366 : Int)/10^30,(-2340381880494291418280059474 : Int)/10^30)
theorem v2544_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 31 34 5) 1) 14) v2544_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2544 : Material (31 : Basis) (34 : Basis) where
  plus := ![v2544_pa,v2544_pb,v2544_pg]
  minus := ![(Primitive.Addresses.material2544 1).one,v2544_mb,v2544_mg]
  upper := v2544_upper
  lower := (Primitive.Addresses.material2544 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2544_pa_checked.trans (by decide +kernel)
    · exact v2544_pb_checked.trans (by decide +kernel)
    · exact v2544_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 31 34 Primitive.Addresses.material2544
    · exact v2544_mb_checked.trans (by decide +kernel)
    · exact v2544_mg_checked.trans (by decide +kernel)
  upper_error := v2544_upper_checked
  lower_error := reuse_lower_error 31 34 Primitive.Addresses.material2544

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
