import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B062
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B063

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1505_pa : Scalar.QComplex := ((999999074432234058090299311237 : Int)/10^30,(-1360564101837223269122122902 : Int)/10^30)
theorem v1505_pa_checked : Scalar.distance (sourceCoefficient 16 90 1 0) v1505_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1505_pb : Scalar.QComplex := ((-587052674302829037540644 : Int)/10^30,(-431477010273222106538325322 : Int)/10^30)
theorem v1505_pb_checked : Scalar.distance (sourceCoefficient 16 90 1 1) v1505_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1505_pg : Scalar.QComplex := ((-93086331726222396209016 : Int)/10^30,(126650038541602824991 : Int)/10^30)
theorem v1505_pg_checked : Scalar.distance (sourceCoefficient 16 90 1 2) v1505_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1505_mb : Scalar.QComplex := ((-959397682578923720221188 : Int)/10^30,(-431476343014593655901486189 : Int)/10^30)
theorem v1505_mb_checked : Scalar.distance (sourceCoefficient 16 90 3 1) v1505_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1505_mg : Scalar.QComplex := ((-93086187772647683598351 : Int)/10^30,(206979303210985423698 : Int)/10^30)
theorem v1505_mg_checked : Scalar.distance (sourceCoefficient 16 90 3 2) v1505_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1505_upper : Scalar.QComplex := ((999995236840870474341127434927 : Int)/10^30,(-3086469758699479718830363209 : Int)/10^30)
theorem v1505_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 90 5) 1) 14) v1505_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1505 : Material (16 : Basis) (90 : Basis) where
  plus := ![v1505_pa,v1505_pb,v1505_pg]
  minus := ![(Primitive.Addresses.material1505 1).one,v1505_mb,v1505_mg]
  upper := v1505_upper
  lower := (Primitive.Addresses.material1505 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1505_pa_checked.trans (by decide +kernel)
    · exact v1505_pb_checked.trans (by decide +kernel)
    · exact v1505_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 90 Primitive.Addresses.material1505
    · exact v1505_mb_checked.trans (by decide +kernel)
    · exact v1505_mg_checked.trans (by decide +kernel)
  upper_error := v1505_upper_checked
  lower_error := reuse_lower_error 16 90 Primitive.Addresses.material1505

def v1506_pa : Scalar.QComplex := ((999999054239906260531017990546 : Int)/10^30,(-1375325159013963160885344435 : Int)/10^30)
theorem v1506_pa_checked : Scalar.distance (sourceCoefficient 16 91 1 0) v1506_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1506_pb : Scalar.QComplex := ((-593421733361807080358421 : Int)/10^30,(-431476998903055860045951269 : Int)/10^30)
theorem v1506_pb_checked : Scalar.distance (sourceCoefficient 16 91 1 1) v1506_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1506_pg : Scalar.QComplex := ((-93086329559913687475032 : Int)/10^30,(128024092084091802010 : Int)/10^30)
theorem v1506_pg_checked : Scalar.distance (sourceCoefficient 16 91 1 2) v1506_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1506_mb : Scalar.QComplex := ((-965766729454468617557808 : Int)/10^30,(-431476326148220526915175097 : Int)/10^30)
theorem v1506_mb_checked : Scalar.distance (sourceCoefficient 16 91 3 1) v1506_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1506_mg : Scalar.QComplex := ((-93086184420593459386389 : Int)/10^30,(208353354372424620785 : Int)/10^30)
theorem v1506_mg_checked : Scalar.distance (sourceCoefficient 16 91 3 2) v1506_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1506_upper : Scalar.QComplex := ((999995191172327176475589859433 : Int)/10^30,(-3101230759041232956500207631 : Int)/10^30)
theorem v1506_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 91 5) 1) 14) v1506_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1506 : Material (16 : Basis) (91 : Basis) where
  plus := ![v1506_pa,v1506_pb,v1506_pg]
  minus := ![(Primitive.Addresses.material1506 1).one,v1506_mb,v1506_mg]
  upper := v1506_upper
  lower := (Primitive.Addresses.material1506 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1506_pa_checked.trans (by decide +kernel)
    · exact v1506_pb_checked.trans (by decide +kernel)
    · exact v1506_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 91 Primitive.Addresses.material1506
    · exact v1506_mb_checked.trans (by decide +kernel)
    · exact v1506_mg_checked.trans (by decide +kernel)
  upper_error := v1506_upper_checked
  lower_error := reuse_lower_error 16 91 Primitive.Addresses.material1506

def v1507_pa : Scalar.QComplex := ((999999009779275745286462529207 : Int)/10^30,(-1407281232722281538566867249 : Int)/10^30)
theorem v1507_pa_checked : Scalar.distance (sourceCoefficient 16 92 1 0) v1507_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1507_pb : Scalar.QComplex := ((-607210048934780961122957 : Int)/10^30,(-431476973858455235655018103 : Int)/10^30)
theorem v1507_pb_checked : Scalar.distance (sourceCoefficient 16 92 1 1) v1507_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1507_pg : Scalar.QComplex := ((-93086324789027302566732 : Int)/10^30,(130998767616383561896 : Int)/10^30)
theorem v1507_pg_checked : Scalar.distance (sourceCoefficient 16 92 1 2) v1507_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1507_mb : Scalar.QComplex := ((-979555018281060081442735 : Int)/10^30,(-431476289204933890977893719 : Int)/10^30)
theorem v1507_mb_checked : Scalar.distance (sourceCoefficient 16 92 3 1) v1507_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1507_mg : Scalar.QComplex := ((-93086177082697840941952 : Int)/10^30,(211328024680048653181 : Int)/10^30)
theorem v1507_mg_checked : Scalar.distance (sourceCoefficient 16 92 3 2) v1507_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1507_upper : Scalar.QComplex := ((999995091558478691920775057116 : Int)/10^30,(-3133186708419718537331807853 : Int)/10^30)
theorem v1507_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 92 5) 1) 14) v1507_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1507 : Material (16 : Basis) (92 : Basis) where
  plus := ![v1507_pa,v1507_pb,v1507_pg]
  minus := ![(Primitive.Addresses.material1507 1).one,v1507_mb,v1507_mg]
  upper := v1507_upper
  lower := (Primitive.Addresses.material1507 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1507_pa_checked.trans (by decide +kernel)
    · exact v1507_pb_checked.trans (by decide +kernel)
    · exact v1507_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 92 Primitive.Addresses.material1507
    · exact v1507_mb_checked.trans (by decide +kernel)
    · exact v1507_mg_checked.trans (by decide +kernel)
  upper_error := v1507_upper_checked
  lower_error := reuse_lower_error 16 92 Primitive.Addresses.material1507

def v1508_pa : Scalar.QComplex := ((999998955688098873986272359388 : Int)/10^30,(-1445206805846374576867496104 : Int)/10^30)
theorem v1508_pa_checked : Scalar.distance (sourceCoefficient 16 93 1 0) v1508_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1508_pb : Scalar.QComplex := ((-623574066334379009704248 : Int)/10^30,(-431476943373076068372402838 : Int)/10^30)
theorem v1508_pb_checked : Scalar.distance (sourceCoefficient 16 93 1 1) v1508_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1508_pg : Scalar.QComplex := ((-93086318983010883171323 : Int)/10^30,(134529122215797279583 : Int)/10^30)
theorem v1508_pg_checked : Scalar.distance (sourceCoefficient 16 93 1 2) v1508_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1508_mb : Scalar.QComplex := ((-995919003280077368757109 : Int)/10^30,(-431476244598156066926732648 : Int)/10^30)
theorem v1508_mb_checked : Scalar.distance (sourceCoefficient 16 93 3 1) v1508_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1508_mg : Scalar.QComplex := ((-93086168230146565366518 : Int)/10^30,(214858372954619331665 : Int)/10^30)
theorem v1508_mg_checked : Scalar.distance (sourceCoefficient 16 93 3 2) v1508_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1508_upper : Scalar.QComplex := ((999994972011283752007427564167 : Int)/10^30,(-3171112131701661291434631059 : Int)/10^30)
theorem v1508_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 93 5) 1) 14) v1508_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1508 : Material (16 : Basis) (93 : Basis) where
  plus := ![v1508_pa,v1508_pb,v1508_pg]
  minus := ![(Primitive.Addresses.material1508 1).one,v1508_mb,v1508_mg]
  upper := v1508_upper
  lower := (Primitive.Addresses.material1508 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1508_pa_checked.trans (by decide +kernel)
    · exact v1508_pb_checked.trans (by decide +kernel)
    · exact v1508_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 93 Primitive.Addresses.material1508
    · exact v1508_mb_checked.trans (by decide +kernel)
    · exact v1508_mg_checked.trans (by decide +kernel)
  upper_error := v1508_upper_checked
  lower_error := reuse_lower_error 16 93 Primitive.Addresses.material1508

def v1509_pa : Scalar.QComplex := ((999998889941464380315880724096 : Int)/10^30,(-1490005315094350841770449787 : Int)/10^30)
theorem v1509_pa_checked : Scalar.distance (sourceCoefficient 16 94 1 0) v1509_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1509_pb : Scalar.QComplex := ((-642903597383728063244820 : Int)/10^30,(-431476906297070488988843681 : Int)/10^30)
theorem v1509_pb_checked : Scalar.distance (sourceCoefficient 16 94 1 1) v1509_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1509_pg : Scalar.QComplex := ((-93086311923585163189752 : Int)/10^30,(138699253492962762837 : Int)/10^30)
theorem v1509_pg_checked : Scalar.distance (sourceCoefficient 16 94 1 2) v1509_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1509_mb : Scalar.QComplex := ((-1015248495137235635710931 : Int)/10^30,(-431476190841649566807668713 : Int)/10^30)
theorem v1509_mb_checked : Scalar.distance (sourceCoefficient 16 94 3 1) v1509_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1509_mg : Scalar.QComplex := ((-93086157572087997478638 : Int)/10^30,(219028496587087904403 : Int)/10^30)
theorem v1509_mg_checked : Scalar.distance (sourceCoefficient 16 94 3 2) v1509_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1509_upper : Scalar.QComplex := ((999994828946584307230994084183 : Int)/10^30,(-3215910460754793786050969049 : Int)/10^30)
theorem v1509_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 94 5) 1) 14) v1509_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1509 : Material (16 : Basis) (94 : Basis) where
  plus := ![v1509_pa,v1509_pb,v1509_pg]
  minus := ![(Primitive.Addresses.material1509 1).one,v1509_mb,v1509_mg]
  upper := v1509_upper
  lower := (Primitive.Addresses.material1509 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1509_pa_checked.trans (by decide +kernel)
    · exact v1509_pb_checked.trans (by decide +kernel)
    · exact v1509_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 94 Primitive.Addresses.material1509
    · exact v1509_mb_checked.trans (by decide +kernel)
    · exact v1509_mg_checked.trans (by decide +kernel)
  upper_error := v1509_upper_checked
  lower_error := reuse_lower_error 16 94 Primitive.Addresses.material1509

def v1510_pa : Scalar.QComplex := ((999998822992533453115923470917 : Int)/10^30,(-1534279488146534482615156653 : Int)/10^30)
theorem v1510_pa_checked : Scalar.distance (sourceCoefficient 16 95 1 0) v1510_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1510_pb : Scalar.QComplex := ((-662006888167942145681648 : Int)/10^30,(-431476868520623555945354086 : Int)/10^30)
theorem v1510_pb_checked : Scalar.distance (sourceCoefficient 16 95 1 1) v1510_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1510_pg : Scalar.QComplex := ((-93086304732644518711261 : Int)/10^30,(142820576079538584701 : Int)/10^30)
theorem v1510_pg_checked : Scalar.distance (sourceCoefficient 16 95 1 2) v1510_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1510_mb : Scalar.QComplex := ((-1034351746209049180460645 : Int)/10^30,(-431476136579937133163191844 : Int)/10^30)
theorem v1510_mb_checked : Scalar.distance (sourceCoefficient 16 95 3 1) v1510_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1510_mg : Scalar.QComplex := ((-93086146824634255779912 : Int)/10^30,(223149811433649065297 : Int)/10^30)
theorem v1510_mg_checked : Scalar.distance (sourceCoefficient 16 95 3 2) v1510_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1510_upper : Scalar.QComplex := ((999994685584546926134264086834 : Int)/10^30,(-3260184452318016254594353684 : Int)/10^30)
theorem v1510_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 95 5) 1) 14) v1510_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1510 : Material (16 : Basis) (95 : Basis) where
  plus := ![v1510_pa,v1510_pb,v1510_pg]
  minus := ![(Primitive.Addresses.material1510 1).one,v1510_mb,v1510_mg]
  upper := v1510_upper
  lower := (Primitive.Addresses.material1510 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1510_pa_checked.trans (by decide +kernel)
    · exact v1510_pb_checked.trans (by decide +kernel)
    · exact v1510_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 95 Primitive.Addresses.material1510
    · exact v1510_mb_checked.trans (by decide +kernel)
    · exact v1510_mg_checked.trans (by decide +kernel)
  upper_error := v1510_upper_checked
  lower_error := reuse_lower_error 16 95 Primitive.Addresses.material1510

def v1511_pa : Scalar.QComplex := ((999998790141385496131044583338 : Int)/10^30,(-1555543559418980340632297068 : Int)/10^30)
theorem v1511_pa_checked : Scalar.distance (sourceCoefficient 16 96 1 0) v1511_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1511_pb : Scalar.QComplex := ((-671181847054342533645221 : Int)/10^30,(-431476849976415645171023872 : Int)/10^30)
theorem v1511_pb_checked : Scalar.distance (sourceCoefficient 16 96 1 1) v1511_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1511_pg : Scalar.QComplex := ((-93086301203294142687932 : Int)/10^30,(144799971494412375856 : Int)/10^30)
theorem v1511_pg_checked : Scalar.distance (sourceCoefficient 16 96 1 2) v1511_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1511_mb : Scalar.QComplex := ((-1043526685676376831803567 : Int)/10^30,(-431476110118159833090061700 : Int)/10^30)
theorem v1511_mb_checked : Scalar.distance (sourceCoefficient 16 96 3 1) v1511_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1511_mg : Scalar.QComplex := ((-93086141587156099519078 : Int)/10^30,(225129203065833062188 : Int)/10^30)
theorem v1511_mg_checked : Scalar.distance (sourceCoefficient 16 96 3 2) v1511_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1511_upper : Scalar.QComplex := ((999994616033589942310584267732 : Int)/10^30,(-3281448435222024664686127805 : Int)/10^30)
theorem v1511_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 96 5) 1) 14) v1511_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1511 : Material (16 : Basis) (96 : Basis) where
  plus := ![v1511_pa,v1511_pb,v1511_pg]
  minus := ![(Primitive.Addresses.material1511 1).one,v1511_mb,v1511_mg]
  upper := v1511_upper
  lower := (Primitive.Addresses.material1511 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1511_pa_checked.trans (by decide +kernel)
    · exact v1511_pb_checked.trans (by decide +kernel)
    · exact v1511_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 96 Primitive.Addresses.material1511
    · exact v1511_mb_checked.trans (by decide +kernel)
    · exact v1511_mg_checked.trans (by decide +kernel)
  upper_error := v1511_upper_checked
  lower_error := reuse_lower_error 16 96 Primitive.Addresses.material1511

def v1512_pa : Scalar.QComplex := ((999998673658008126430840733339 : Int)/10^30,(-1628705689977185200165231469 : Int)/10^30)
theorem v1512_pa_checked : Scalar.distance (sourceCoefficient 16 97 1 0) v1512_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1512_pb : Scalar.QComplex := ((-702749625581745464280424 : Int)/10^30,(-431476784185147249192544694 : Int)/10^30)
theorem v1512_pb_checked : Scalar.distance (sourceCoefficient 16 97 1 1) v1512_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1512_pg : Scalar.QComplex := ((-93086288684919487645131 : Int)/10^30,(151610369127186218515 : Int)/10^30)
theorem v1512_pg_checked : Scalar.distance (sourceCoefficient 16 97 1 2) v1512_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1512_mb : Scalar.QComplex := ((-1075094395674751600938822 : Int)/10^30,(-431476017085344825025550116 : Int)/10^30)
theorem v1512_mb_checked : Scalar.distance (sourceCoefficient 16 97 3 1) v1512_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1512_mg : Scalar.QComplex := ((-93086123191719677478519 : Int)/10^30,(231939587359991094980 : Int)/10^30)
theorem v1512_mg_checked : Scalar.distance (sourceCoefficient 16 97 3 2) v1512_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1512_upper : Scalar.QComplex := ((999994373279185934093435601633 : Int)/10^30,(-3354610255774088234685142170 : Int)/10^30)
theorem v1512_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 97 5) 1) 14) v1512_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1512 : Material (16 : Basis) (97 : Basis) where
  plus := ![v1512_pa,v1512_pb,v1512_pg]
  minus := ![(Primitive.Addresses.material1512 1).one,v1512_mb,v1512_mg]
  upper := v1512_upper
  lower := (Primitive.Addresses.material1512 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1512_pa_checked.trans (by decide +kernel)
    · exact v1512_pb_checked.trans (by decide +kernel)
    · exact v1512_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 97 Primitive.Addresses.material1512
    · exact v1512_mb_checked.trans (by decide +kernel)
    · exact v1512_mg_checked.trans (by decide +kernel)
  upper_error := v1512_upper_checked
  lower_error := reuse_lower_error 16 97 Primitive.Addresses.material1512

def v1513_pa : Scalar.QComplex := ((999999988473595527205714438839 : Int)/10^30,(-151831514557191225602238693 : Int)/10^30)
theorem v1513_pa_checked : Scalar.distance (sourceCoefficient 17 18 1 0) v1513_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1513_pb : Scalar.QComplex := ((-65511885505471847982977 : Int)/10^30,(-431477515991442144984721434 : Int)/10^30)
theorem v1513_pb_checked : Scalar.distance (sourceCoefficient 17 18 1 1) v1513_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1513_pg : Scalar.QComplex := ((-93086428820159668910570 : Int)/10^30,(14133453635392920813 : Int)/10^30)
theorem v1513_pg_checked : Scalar.distance (sourceCoefficient 17 18 1 2) v1513_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1513_mb : Scalar.QComplex := ((-437857524387084981529426 : Int)/10^30,(-431477298798836799298656272 : Int)/10^30)
theorem v1513_mb_checked : Scalar.distance (sourceCoefficient 17 18 3 1) v1513_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1513_mg : Scalar.QComplex := ((-93086381963294018981245 : Int)/10^30,(94462843987537259804 : Int)/10^30)
theorem v1513_mg_checked : Scalar.distance (sourceCoefficient 17 18 3 2) v1513_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1513_upper : Scalar.QComplex := ((999998237043660867817431377570 : Int)/10^30,(-1877740549237117436249580541 : Int)/10^30)
theorem v1513_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 18 5) 1) 14) v1513_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1513 : Material (17 : Basis) (18 : Basis) where
  plus := ![v1513_pa,v1513_pb,v1513_pg]
  minus := ![(Primitive.Addresses.material1513 1).one,v1513_mb,v1513_mg]
  upper := v1513_upper
  lower := (Primitive.Addresses.material1513 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1513_pa_checked.trans (by decide +kernel)
    · exact v1513_pb_checked.trans (by decide +kernel)
    · exact v1513_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 18 Primitive.Addresses.material1513
    · exact v1513_mb_checked.trans (by decide +kernel)
    · exact v1513_mg_checked.trans (by decide +kernel)
  upper_error := v1513_upper_checked
  lower_error := reuse_lower_error 17 18 Primitive.Addresses.material1513

def v1514_pa : Scalar.QComplex := ((999999985974694439183822927861 : Int)/10^30,(-167483166094157528826361523 : Int)/10^30)
theorem v1514_pa_checked : Scalar.distance (sourceCoefficient 17 19 1 0) v1514_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1514_pb : Scalar.QComplex := ((-72265221298281664320096 : Int)/10^30,(-431477514845360623584792345 : Int)/10^30)
theorem v1514_pb_checked : Scalar.distance (sourceCoefficient 17 19 1 1) v1514_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1514_pg : Scalar.QComplex := ((-93086428580225669320083 : Int)/10^30,(15590409997674132210 : Int)/10^30)
theorem v1514_pg_checked : Scalar.distance (sourceCoefficient 17 19 1 2) v1514_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1514_mb : Scalar.QComplex := ((-444610856676302504137910 : Int)/10^30,(-431477291824931074395581692 : Int)/10^30)
theorem v1514_mb_checked : Scalar.distance (sourceCoefficient 17 19 3 1) v1514_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1514_mg : Scalar.QComplex := ((-93086380466072386959137 : Int)/10^30,(95919799600274795908 : Int)/10^30)
theorem v1514_mg_checked : Scalar.distance (sourceCoefficient 17 19 3 2) v1514_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1514_upper : Scalar.QComplex := ((999998207531432855547060426696 : Int)/10^30,(-1893392173149910767914624411 : Int)/10^30)
theorem v1514_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 19 5) 1) 14) v1514_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1514 : Material (17 : Basis) (19 : Basis) where
  plus := ![v1514_pa,v1514_pb,v1514_pg]
  minus := ![(Primitive.Addresses.material1514 1).one,v1514_mb,v1514_mg]
  upper := v1514_upper
  lower := (Primitive.Addresses.material1514 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1514_pa_checked.trans (by decide +kernel)
    · exact v1514_pb_checked.trans (by decide +kernel)
    · exact v1514_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 19 Primitive.Addresses.material1514
    · exact v1514_mb_checked.trans (by decide +kernel)
    · exact v1514_mg_checked.trans (by decide +kernel)
  upper_error := v1514_upper_checked
  lower_error := reuse_lower_error 17 19 Primitive.Addresses.material1514

def v1515_pa : Scalar.QComplex := ((999999985500896393613831122949 : Int)/10^30,(-170288599156104200907227745 : Int)/10^30)
theorem v1515_pa_checked : Scalar.distance (sourceCoefficient 17 20 1 0) v1515_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1515_pb : Scalar.QComplex := ((-73475702598187359467395 : Int)/10^30,(-431477514625040061045311272 : Int)/10^30)
theorem v1515_pb_checked : Scalar.distance (sourceCoefficient 17 20 1 1) v1515_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1515_pg : Scalar.QComplex := ((-93086428534407741415170 : Int)/10^30,(15851557745402478195 : Int)/10^30)
theorem v1515_pg_checked : Scalar.distance (sourceCoefficient 17 20 1 2) v1515_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1515_mb : Scalar.QComplex := ((-445821337335363967000175 : Int)/10^30,(-431477290560019750126842748 : Int)/10^30)
theorem v1515_mb_checked : Scalar.distance (sourceCoefficient 17 20 3 1) v1515_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1515_mg : Scalar.QComplex := ((-93086380194895731482714 : Int)/10^30,(96180947211227092153 : Int)/10^30)
theorem v1515_mg_checked : Scalar.distance (sourceCoefficient 17 20 3 2) v1515_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1515_upper : Scalar.QComplex := ((999998202215712557622926267213 : Int)/10^30,(-1896197601215761999512082164 : Int)/10^30)
theorem v1515_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 20 5) 1) 14) v1515_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1515 : Material (17 : Basis) (20 : Basis) where
  plus := ![v1515_pa,v1515_pb,v1515_pg]
  minus := ![(Primitive.Addresses.material1515 1).one,v1515_mb,v1515_mg]
  upper := v1515_upper
  lower := (Primitive.Addresses.material1515 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1515_pa_checked.trans (by decide +kernel)
    · exact v1515_pb_checked.trans (by decide +kernel)
    · exact v1515_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 20 Primitive.Addresses.material1515
    · exact v1515_mb_checked.trans (by decide +kernel)
    · exact v1515_mg_checked.trans (by decide +kernel)
  upper_error := v1515_upper_checked
  lower_error := reuse_lower_error 17 20 Primitive.Addresses.material1515

def v1516_pa : Scalar.QComplex := ((999999975069130618054967648768 : Int)/10^30,(-223297420814352033041156901 : Int)/10^30)
theorem v1516_pa_checked : Scalar.distance (sourceCoefficient 17 21 1 0) v1516_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1516_pb : Scalar.QComplex := ((-96347817437573194592629 : Int)/10^30,(-431477509611010085372880742 : Int)/10^30)
theorem v1516_pb_checked : Scalar.distance (sourceCoefficient 17 21 1 1) v1516_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1516_pg : Scalar.QComplex := ((-93086427508019493931573 : Int)/10^30,(20785959693574949893 : Int)/10^30)
theorem v1516_pg_checked : Scalar.distance (sourceCoefficient 17 21 1 2) v1516_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1516_mb : Scalar.QComplex := ((-468693439331534094656508 : Int)/10^30,(-431477265808386656829395715 : Int)/10^30)
theorem v1516_mb_checked : Scalar.distance (sourceCoefficient 17 21 3 1) v1516_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1516_mg : Scalar.QComplex := ((-93086374910341222111439 : Int)/10^30,(101115346436369374469 : Int)/10^30)
theorem v1516_mg_checked : Scalar.distance (sourceCoefficient 17 21 3 2) v1516_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1516_upper : Scalar.QComplex := ((999998100295545059553619290026 : Int)/10^30,(-1949206325919315459074434715 : Int)/10^30)
theorem v1516_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 21 5) 1) 14) v1516_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1516 : Material (17 : Basis) (21 : Basis) where
  plus := ![v1516_pa,v1516_pb,v1516_pg]
  minus := ![(Primitive.Addresses.material1516 1).one,v1516_mb,v1516_mg]
  upper := v1516_upper
  lower := (Primitive.Addresses.material1516 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1516_pa_checked.trans (by decide +kernel)
    · exact v1516_pb_checked.trans (by decide +kernel)
    · exact v1516_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 21 Primitive.Addresses.material1516
    · exact v1516_mb_checked.trans (by decide +kernel)
    · exact v1516_mg_checked.trans (by decide +kernel)
  upper_error := v1516_upper_checked
  lower_error := reuse_lower_error 17 21 Primitive.Addresses.material1516

def v1517_pa : Scalar.QComplex := ((999999974756860356235260446059 : Int)/10^30,(-224691518866007446002714130 : Int)/10^30)
theorem v1517_pa_checked : Scalar.distance (sourceCoefficient 17 22 1 0) v1517_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1517_pb : Scalar.QComplex := ((-96949339403794820033547 : Int)/10^30,(-431477509457327940256556514 : Int)/10^30)
theorem v1517_pb_checked : Scalar.distance (sourceCoefficient 17 22 1 1) v1517_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1517_pg : Scalar.QComplex := ((-93086427476907833511304 : Int)/10^30,(20915731303575596422 : Int)/10^30)
theorem v1517_pg_checked : Scalar.distance (sourceCoefficient 17 22 1 2) v1517_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1517_mb : Scalar.QComplex := ((-469294960941160831512668 : Int)/10^30,(-431477265135618203630368227 : Int)/10^30)
theorem v1517_mb_checked : Scalar.distance (sourceCoefficient 17 22 3 1) v1517_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1517_mg : Scalar.QComplex := ((-93086374767242518541254 : Int)/10^30,(101245117971202158014 : Int)/10^30)
theorem v1517_mg_checked : Scalar.distance (sourceCoefficient 17 22 3 2) v1517_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1517_upper : Scalar.QComplex := ((999998097577188497253846810111 : Int)/10^30,(-1950600421355675443392117319 : Int)/10^30)
theorem v1517_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 22 5) 1) 14) v1517_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1517 : Material (17 : Basis) (22 : Basis) where
  plus := ![v1517_pa,v1517_pb,v1517_pg]
  minus := ![(Primitive.Addresses.material1517 1).one,v1517_mb,v1517_mg]
  upper := v1517_upper
  lower := (Primitive.Addresses.material1517 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1517_pa_checked.trans (by decide +kernel)
    · exact v1517_pb_checked.trans (by decide +kernel)
    · exact v1517_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 22 Primitive.Addresses.material1517
    · exact v1517_mb_checked.trans (by decide +kernel)
    · exact v1517_mg_checked.trans (by decide +kernel)
  upper_error := v1517_upper_checked
  lower_error := reuse_lower_error 17 22 Primitive.Addresses.material1517

def v1518_pa : Scalar.QComplex := ((999999972387437224917388308612 : Int)/10^30,(-235000265505619376895695913 : Int)/10^30)
theorem v1518_pa_checked : Scalar.distance (sourceCoefficient 17 23 1 0) v1518_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1518_pb : Scalar.QComplex := ((-101397331806803276102605 : Int)/10^30,(-431477508286212772897030014 : Int)/10^30)
theorem v1518_pb_checked : Scalar.distance (sourceCoefficient 17 23 1 1) v1518_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1518_pg : Scalar.QComplex := ((-93086427240299790366108 : Int)/10^30,(21875335720474051562 : Int)/10^30)
theorem v1518_pg_checked : Scalar.distance (sourceCoefficient 17 23 1 2) v1518_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1518_mb : Scalar.QComplex := ((-473742950677358788284339 : Int)/10^30,(-431477260126086358675470653 : Int)/10^30)
theorem v1518_mb_checked : Scalar.distance (sourceCoefficient 17 23 3 1) v1518_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1518_mg : Scalar.QComplex := ((-93086373702539170691252 : Int)/10^30,(102204721826613947850 : Int)/10^30)
theorem v1518_mg_checked : Scalar.distance (sourceCoefficient 17 23 3 2) v1518_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1518_upper : Scalar.QComplex := ((999998077415807397132951053177 : Int)/10^30,(-1960909148552210832760756003 : Int)/10^30)
theorem v1518_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 23 5) 1) 14) v1518_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1518 : Material (17 : Basis) (23 : Basis) where
  plus := ![v1518_pa,v1518_pb,v1518_pg]
  minus := ![(Primitive.Addresses.material1518 1).one,v1518_mb,v1518_mg]
  upper := v1518_upper
  lower := (Primitive.Addresses.material1518 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1518_pa_checked.trans (by decide +kernel)
    · exact v1518_pb_checked.trans (by decide +kernel)
    · exact v1518_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 23 Primitive.Addresses.material1518
    · exact v1518_mb_checked.trans (by decide +kernel)
    · exact v1518_mg_checked.trans (by decide +kernel)
  upper_error := v1518_upper_checked
  lower_error := reuse_lower_error 17 23 Primitive.Addresses.material1518

def v1519_pa : Scalar.QComplex := ((999999959117373040681007556382 : Int)/10^30,(-285946240134835131551684780 : Int)/10^30)
theorem v1519_pa_checked : Scalar.distance (sourceCoefficient 17 24 1 0) v1519_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1519_pb : Scalar.QComplex := ((-123379374329615557763580 : Int)/10^30,(-431477501600875384414157475 : Int)/10^30)
theorem v1519_pb_checked : Scalar.distance (sourceCoefficient 17 24 1 1) v1519_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1519_pg : Scalar.QComplex := ((-93086425901525107137883 : Int)/10^30,(26617714582333130913 : Int)/10^30)
theorem v1519_pg_checked : Scalar.distance (sourceCoefficient 17 24 1 2) v1519_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1519_mb : Scalar.QComplex := ((-495724979246106939887364 : Int)/10^30,(-431477234471238796705665177 : Int)/10^30)
theorem v1519_mb_checked : Scalar.distance (sourceCoefficient 17 24 3 1) v1519_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1519_mg : Scalar.QComplex := ((-93086368271305616980790 : Int)/10^30,(106947097767366384058 : Int)/10^30)
theorem v1519_mg_checked : Scalar.distance (sourceCoefficient 17 24 3 2) v1519_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1519_upper : Scalar.QComplex := ((999997976217632549786946124763 : Int)/10^30,(-2011855024400454980597285070 : Int)/10^30)
theorem v1519_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 24 5) 1) 14) v1519_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1519 : Material (17 : Basis) (24 : Basis) where
  plus := ![v1519_pa,v1519_pb,v1519_pg]
  minus := ![(Primitive.Addresses.material1519 1).one,v1519_mb,v1519_mg]
  upper := v1519_upper
  lower := (Primitive.Addresses.material1519 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1519_pa_checked.trans (by decide +kernel)
    · exact v1519_pb_checked.trans (by decide +kernel)
    · exact v1519_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 24 Primitive.Addresses.material1519
    · exact v1519_mb_checked.trans (by decide +kernel)
    · exact v1519_mg_checked.trans (by decide +kernel)
  upper_error := v1519_upper_checked
  lower_error := reuse_lower_error 17 24 Primitive.Addresses.material1519

def v1520_pa : Scalar.QComplex := ((999999952280947779126263251212 : Int)/10^30,(-308930578228571489266523266 : Int)/10^30)
theorem v1520_pa_checked : Scalar.distance (sourceCoefficient 17 25 1 0) v1520_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1520_pb : Scalar.QComplex := ((-133296599340198388763802 : Int)/10^30,(-431477498095988250341464908 : Int)/10^30)
theorem v1520_pb_checked : Scalar.distance (sourceCoefficient 17 25 1 1) v1520_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1520_pg : Scalar.QComplex := ((-93086425205265876615139 : Int)/10^30,(28757244536161912496 : Int)/10^30)
theorem v1520_pg_checked : Scalar.distance (sourceCoefficient 17 25 1 2) v1520_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1520_mb : Scalar.QComplex := ((-505642197539493917426084 : Int)/10^30,(-431477222408234438763505718 : Int)/10^30)
theorem v1520_mb_checked : Scalar.distance (sourceCoefficient 17 25 3 1) v1520_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1520_mg : Scalar.QComplex := ((-93086365728728656404978 : Int)/10^30,(109086626323710024891 : Int)/10^30)
theorem v1520_mg_checked : Scalar.distance (sourceCoefficient 17 25 3 2) v1520_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1520_upper : Scalar.QComplex := ((999997929712335043359390380750 : Int)/10^30,(-2034839316462669871915585036 : Int)/10^30)
theorem v1520_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 25 5) 1) 14) v1520_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1520 : Material (17 : Basis) (25 : Basis) where
  plus := ![v1520_pa,v1520_pb,v1520_pg]
  minus := ![(Primitive.Addresses.material1520 1).one,v1520_mb,v1520_mg]
  upper := v1520_upper
  lower := (Primitive.Addresses.material1520 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1520_pa_checked.trans (by decide +kernel)
    · exact v1520_pb_checked.trans (by decide +kernel)
    · exact v1520_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 25 Primitive.Addresses.material1520
    · exact v1520_mb_checked.trans (by decide +kernel)
    · exact v1520_mg_checked.trans (by decide +kernel)
  upper_error := v1520_upper_checked
  lower_error := reuse_lower_error 17 25 Primitive.Addresses.material1520

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
