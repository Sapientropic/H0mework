import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B101
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B102

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2433_pa : Scalar.QComplex := ((999999581445206038745106408040 : Int)/10^30,(-914936835379576484146748023 : Int)/10^30)
theorem v2433_pa_checked : Scalar.distance (sourceCoefficient 29 56 1 0) v2433_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2433_pb : Scalar.QComplex := ((-394774669042147917398224 : Int)/10^30,(-431477331048256470110411129 : Int)/10^30)
theorem v2433_pb_checked : Scalar.distance (sourceCoefficient 29 56 1 1) v2433_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2433_pg : Scalar.QComplex := ((-93086389926042105219059 : Int)/10^30,(85168202663401770266 : Int)/10^30)
theorem v2433_pg_checked : Scalar.distance (sourceCoefficient 29 56 1 2) v2433_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2433_mb : Scalar.QComplex := ((-767120025726538982103174 : Int)/10^30,(-431476829716767240348852978 : Int)/10^30)
theorem v2433_mb_checked : Scalar.distance (sourceCoefficient 29 56 3 1) v2433_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2433_mg : Scalar.QComplex := ((-93086281769401812508746 : Int)/10^30,(165497533002190866283 : Int)/10^30)
theorem v2433_mg_checked : Scalar.distance (sourceCoefficient 29 56 3 2) v2433_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2433_upper : Scalar.QComplex := ((999996512965322234815723831827 : Int)/10^30,(-2640844031009693047713674551 : Int)/10^30)
theorem v2433_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 56 5) 1) 14) v2433_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2433 : Material (29 : Basis) (56 : Basis) where
  plus := ![v2433_pa,v2433_pb,v2433_pg]
  minus := ![(Primitive.Addresses.material2433 1).one,v2433_mb,v2433_mg]
  upper := v2433_upper
  lower := (Primitive.Addresses.material2433 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2433_pa_checked.trans (by decide +kernel)
    · exact v2433_pb_checked.trans (by decide +kernel)
    · exact v2433_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 56 Primitive.Addresses.material2433
    · exact v2433_mb_checked.trans (by decide +kernel)
    · exact v2433_mg_checked.trans (by decide +kernel)
  upper_error := v2433_upper_checked
  lower_error := reuse_lower_error 29 56 Primitive.Addresses.material2433

def v2434_pa : Scalar.QComplex := ((999999570599852497641524410965 : Int)/10^30,(-926714686740331247746495268 : Int)/10^30)
theorem v2434_pa_checked : Scalar.distance (sourceCoefficient 29 57 1 0) v2434_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2434_pb : Scalar.QComplex := ((-399856546464359634205485 : Int)/10^30,(-431477325747768990984389773 : Int)/10^30)
theorem v2434_pb_checked : Scalar.distance (sourceCoefficient 29 57 1 1) v2434_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2434_pg : Scalar.QComplex := ((-93086388849504158477903 : Int)/10^30,(86264560724472009199 : Int)/10^30)
theorem v2434_pg_checked : Scalar.distance (sourceCoefficient 29 57 1 2) v2434_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2434_mb : Scalar.QComplex := ((-772201896682453511957685 : Int)/10^30,(-431476820030850398730551549 : Int)/10^30)
theorem v2434_mb_checked : Scalar.distance (sourceCoefficient 29 57 3 1) v2434_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2434_mg : Scalar.QComplex := ((-93086279746756638042319 : Int)/10^30,(166593889726033130473 : Int)/10^30)
theorem v2434_mg_checked : Scalar.distance (sourceCoefficient 29 57 3 2) v2434_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2434_upper : Scalar.QComplex := ((999996481792481876258487624463 : Int)/10^30,(-2652621846110625403920064230 : Int)/10^30)
theorem v2434_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 57 5) 1) 14) v2434_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2434 : Material (29 : Basis) (57 : Basis) where
  plus := ![v2434_pa,v2434_pb,v2434_pg]
  minus := ![(Primitive.Addresses.material2434 1).one,v2434_mb,v2434_mg]
  upper := v2434_upper
  lower := (Primitive.Addresses.material2434 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2434_pa_checked.trans (by decide +kernel)
    · exact v2434_pb_checked.trans (by decide +kernel)
    · exact v2434_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 57 Primitive.Addresses.material2434
    · exact v2434_mb_checked.trans (by decide +kernel)
    · exact v2434_mg_checked.trans (by decide +kernel)
  upper_error := v2434_upper_checked
  lower_error := reuse_lower_error 29 57 Primitive.Addresses.material2434

def v2435_pa : Scalar.QComplex := ((999999564657216129687311449747 : Int)/10^30,(-933105234267435619740184176 : Int)/10^30)
theorem v2435_pa_checked : Scalar.distance (sourceCoefficient 29 58 1 0) v2435_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2435_pb : Scalar.QComplex := ((-402613923683256963889285 : Int)/10^30,(-431477322838377945947160547 : Int)/10^30)
theorem v2435_pb_checked : Scalar.distance (sourceCoefficient 29 58 1 1) v2435_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2435_pg : Scalar.QComplex := ((-93086388259080533274601 : Int)/10^30,(86859433937226585191 : Int)/10^30)
theorem v2435_pg_checked : Scalar.distance (sourceCoefficient 29 58 1 2) v2435_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2435_mb : Scalar.QComplex := ((-774959270363979846922997 : Int)/10^30,(-431476814741968084744055116 : Int)/10^30)
theorem v2435_mb_checked : Scalar.distance (sourceCoefficient 29 58 3 1) v2435_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2435_mg : Scalar.QComplex := ((-93086278642984442168451 : Int)/10^30,(167188762207780225450 : Int)/10^30)
theorem v2435_mg_checked : Scalar.distance (sourceCoefficient 29 58 3 2) v2435_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2435_upper : Scalar.QComplex := ((999996464820349073323859697019 : Int)/10^30,(-2659012373863308661408190669 : Int)/10^30)
theorem v2435_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 58 5) 1) 14) v2435_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2435 : Material (29 : Basis) (58 : Basis) where
  plus := ![v2435_pa,v2435_pb,v2435_pg]
  minus := ![(Primitive.Addresses.material2435 1).one,v2435_mb,v2435_mg]
  upper := v2435_upper
  lower := (Primitive.Addresses.material2435 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2435_pa_checked.trans (by decide +kernel)
    · exact v2435_pb_checked.trans (by decide +kernel)
    · exact v2435_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 58 Primitive.Addresses.material2435
    · exact v2435_mb_checked.trans (by decide +kernel)
    · exact v2435_mg_checked.trans (by decide +kernel)
  upper_error := v2435_upper_checked
  lower_error := reuse_lower_error 29 58 Primitive.Addresses.material2435

def v2436_pa : Scalar.QComplex := ((999999548112076852071650989217 : Int)/10^30,(-950671153497970406926607207 : Int)/10^30)
theorem v2436_pa_checked : Scalar.distance (sourceCoefficient 29 59 1 0) v2436_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2436_pb : Scalar.QComplex := ((-410193221854608304527036 : Int)/10^30,(-431477314720185116734960368 : Int)/10^30)
theorem v2436_pb_checked : Scalar.distance (sourceCoefficient 29 59 1 1) v2436_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2436_pg : Scalar.QComplex := ((-93086386613312089981296 : Int)/10^30,(88494582526268543191 : Int)/10^30)
theorem v2436_pg_checked : Scalar.distance (sourceCoefficient 29 59 1 2) v2436_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2436_mb : Scalar.QComplex := ((-782538558707577305550230 : Int)/10^30,(-431476800083185315347657013 : Int)/10^30)
theorem v2436_mb_checked : Scalar.distance (sourceCoefficient 29 59 3 1) v2436_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2436_mg : Scalar.QComplex := ((-93086275586157023685386 : Int)/10^30,(168823908767757589864 : Int)/10^30)
theorem v2436_mg_checked : Scalar.distance (sourceCoefficient 29 59 3 2) v2436_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2436_upper : Scalar.QComplex := ((999996417958051413590908014408 : Int)/10^30,(-2676578238376060762680221445 : Int)/10^30)
theorem v2436_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 59 5) 1) 14) v2436_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2436 : Material (29 : Basis) (59 : Basis) where
  plus := ![v2436_pa,v2436_pb,v2436_pg]
  minus := ![(Primitive.Addresses.material2436 1).one,v2436_mb,v2436_mg]
  upper := v2436_upper
  lower := (Primitive.Addresses.material2436 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2436_pa_checked.trans (by decide +kernel)
    · exact v2436_pb_checked.trans (by decide +kernel)
    · exact v2436_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 59 Primitive.Addresses.material2436
    · exact v2436_mb_checked.trans (by decide +kernel)
    · exact v2436_mg_checked.trans (by decide +kernel)
  upper_error := v2436_upper_checked
  lower_error := reuse_lower_error 29 59 Primitive.Addresses.material2436

def v2437_pa : Scalar.QComplex := ((999999528642429614901926121675 : Int)/10^30,(-970935074344436785839775675 : Int)/10^30)
theorem v2437_pa_checked : Scalar.distance (sourceCoefficient 29 60 1 0) v2437_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2437_pb : Scalar.QComplex := ((-418936646807746943475430 : Int)/10^30,(-431477305134586478799418189 : Int)/10^30)
theorem v2437_pb_checked : Scalar.distance (sourceCoefficient 29 60 1 1) v2437_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2437_pg : Scalar.QComplex := ((-93086384673139481609359 : Int)/10^30,(90380878424780787107 : Int)/10^30)
theorem v2437_pg_checked : Scalar.distance (sourceCoefficient 29 60 1 2) v2437_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2437_mb : Scalar.QComplex := ((-791281972133199334982498 : Int)/10^30,(-431476782952408301251671404 : Int)/10^30)
theorem v2437_mb_checked : Scalar.distance (sourceCoefficient 29 60 3 1) v2437_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2437_mg : Scalar.QComplex := ((-93086272018196732925883 : Int)/10^30,(170710202289634083888 : Int)/10^30)
theorem v2437_mg_checked : Scalar.distance (sourceCoefficient 29 60 3 2) v2437_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2437_upper : Scalar.QComplex := ((999996363514744121711664435109 : Int)/10^30,(-2696842095438952549381077671 : Int)/10^30)
theorem v2437_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 60 5) 1) 14) v2437_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2437 : Material (29 : Basis) (60 : Basis) where
  plus := ![v2437_pa,v2437_pb,v2437_pg]
  minus := ![(Primitive.Addresses.material2437 1).one,v2437_mb,v2437_mg]
  upper := v2437_upper
  lower := (Primitive.Addresses.material2437 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2437_pa_checked.trans (by decide +kernel)
    · exact v2437_pb_checked.trans (by decide +kernel)
    · exact v2437_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 60 Primitive.Addresses.material2437
    · exact v2437_mb_checked.trans (by decide +kernel)
    · exact v2437_mg_checked.trans (by decide +kernel)
  upper_error := v2437_upper_checked
  lower_error := reuse_lower_error 29 60 Primitive.Addresses.material2437

def v2438_pa : Scalar.QComplex := ((999999522936229283250884906246 : Int)/10^30,(-976794407152117604560259043 : Int)/10^30)
theorem v2438_pa_checked : Scalar.distance (sourceCoefficient 29 61 1 0) v2438_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2438_pb : Scalar.QComplex := ((-421464816783752043194217 : Int)/10^30,(-431477302318871723681755604 : Int)/10^30)
theorem v2438_pb_checked : Scalar.distance (sourceCoefficient 29 61 1 1) v2438_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2438_pg : Scalar.QComplex := ((-93086384103825153433051 : Int)/10^30,(90926302752275043279 : Int)/10^30)
theorem v2438_pg_checked : Scalar.distance (sourceCoefficient 29 61 1 2) v2438_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2438_mb : Scalar.QComplex := ((-793810138738016190977170 : Int)/10^30,(-431476777954997769809764144 : Int)/10^30)
theorem v2438_mb_checked : Scalar.distance (sourceCoefficient 29 61 3 1) v2438_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2438_mg : Scalar.QComplex := ((-93086270978205987103590 : Int)/10^30,(171255625922749311561 : Int)/10^30)
theorem v2438_mg_checked : Scalar.distance (sourceCoefficient 29 61 3 2) v2438_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2438_upper : Scalar.QComplex := ((999996347695875417238663489150 : Int)/10^30,(-2702701409671461326662629857 : Int)/10^30)
theorem v2438_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 61 5) 1) 14) v2438_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2438 : Material (29 : Basis) (61 : Basis) where
  plus := ![v2438_pa,v2438_pb,v2438_pg]
  minus := ![(Primitive.Addresses.material2438 1).one,v2438_mb,v2438_mg]
  upper := v2438_upper
  lower := (Primitive.Addresses.material2438 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2438_pa_checked.trans (by decide +kernel)
    · exact v2438_pb_checked.trans (by decide +kernel)
    · exact v2438_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 61 Primitive.Addresses.material2438
    · exact v2438_mb_checked.trans (by decide +kernel)
    · exact v2438_mg_checked.trans (by decide +kernel)
  upper_error := v2438_upper_checked
  lower_error := reuse_lower_error 29 61 Primitive.Addresses.material2438

def v2439_pa : Scalar.QComplex := ((999999514584185022053200903685 : Int)/10^30,(-985307766298114676282515286 : Int)/10^30)
theorem v2439_pa_checked : Scalar.distance (sourceCoefficient 29 62 1 0) v2439_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2439_pb : Scalar.QComplex := ((-425138139259235106484082 : Int)/10^30,(-431477298192561941788960925 : Int)/10^30)
theorem v2439_pb_checked : Scalar.distance (sourceCoefficient 29 62 1 1) v2439_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2439_pg : Scalar.QComplex := ((-93086383269991662697803 : Int)/10^30,(91718780894272453603 : Int)/10^30)
theorem v2439_pg_checked : Scalar.distance (sourceCoefficient 29 62 1 2) v2439_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2439_mb : Scalar.QComplex := ((-797483456284933917834475 : Int)/10^30,(-431476770658777668291662352 : Int)/10^30)
theorem v2439_mb_checked : Scalar.distance (sourceCoefficient 29 62 3 1) v2439_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2439_mg : Scalar.QComplex := ((-93086269460499862189464 : Int)/10^30,(172048103050110143540 : Int)/10^30)
theorem v2439_mg_checked : Scalar.distance (sourceCoefficient 29 62 3 2) v2439_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2439_upper : Scalar.QComplex := ((999996324650558035347506652156 : Int)/10^30,(-2711214741722939296546588259 : Int)/10^30)
theorem v2439_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 62 5) 1) 14) v2439_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2439 : Material (29 : Basis) (62 : Basis) where
  plus := ![v2439_pa,v2439_pb,v2439_pg]
  minus := ![(Primitive.Addresses.material2439 1).one,v2439_mb,v2439_mg]
  upper := v2439_upper
  lower := (Primitive.Addresses.material2439 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2439_pa_checked.trans (by decide +kernel)
    · exact v2439_pb_checked.trans (by decide +kernel)
    · exact v2439_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 62 Primitive.Addresses.material2439
    · exact v2439_mb_checked.trans (by decide +kernel)
    · exact v2439_mg_checked.trans (by decide +kernel)
  upper_error := v2439_upper_checked
  lower_error := reuse_lower_error 29 62 Primitive.Addresses.material2439

def v2440_pa : Scalar.QComplex := ((999999489845907512629234730233 : Int)/10^30,(-1010102927783868691488426485 : Int)/10^30)
theorem v2440_pa_checked : Scalar.distance (sourceCoefficient 29 63 1 0) v2440_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2440_pb : Scalar.QComplex := ((-435836692141188794475657 : Int)/10^30,(-431477285937114314445884626 : Int)/10^30)
theorem v2440_pb_checked : Scalar.distance (sourceCoefficient 29 63 1 1) v2440_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2440_pg : Scalar.QComplex := ((-93086380796605093810813 : Int)/10^30,(94026873747649342588 : Int)/10^30)
theorem v2440_pg_checked : Scalar.distance (sourceCoefficient 29 63 1 2) v2440_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2440_mb : Scalar.QComplex := ((-808181994607428082327627 : Int)/10^30,(-431476749170965312020685031 : Int)/10^30)
theorem v2440_mb_checked : Scalar.distance (sourceCoefficient 29 63 3 1) v2440_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2440_mg : Scalar.QComplex := ((-93086264995334034436291 : Int)/10^30,(174356192909657366405 : Int)/10^30)
theorem v2440_mg_checked : Scalar.distance (sourceCoefficient 29 63 3 2) v2440_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2440_upper : Scalar.QComplex := ((999996257118118045749141475543 : Int)/10^30,(-2736009823583190180730967453 : Int)/10^30)
theorem v2440_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 63 5) 1) 14) v2440_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2440 : Material (29 : Basis) (63 : Basis) where
  plus := ![v2440_pa,v2440_pb,v2440_pg]
  minus := ![(Primitive.Addresses.material2440 1).one,v2440_mb,v2440_mg]
  upper := v2440_upper
  lower := (Primitive.Addresses.material2440 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2440_pa_checked.trans (by decide +kernel)
    · exact v2440_pb_checked.trans (by decide +kernel)
    · exact v2440_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 63 Primitive.Addresses.material2440
    · exact v2440_mb_checked.trans (by decide +kernel)
    · exact v2440_mg_checked.trans (by decide +kernel)
  upper_error := v2440_upper_checked
  lower_error := reuse_lower_error 29 63 Primitive.Addresses.material2440

def v2441_pa : Scalar.QComplex := ((999999453422716085906928156759 : Int)/10^30,(-1045540180519839635674807100 : Int)/10^30)
theorem v2441_pa_checked : Scalar.distance (sourceCoefficient 29 64 1 0) v2441_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2441_pb : Scalar.QComplex := ((-451127067049613805764575 : Int)/10^30,(-431477267807639694876789657 : Int)/10^30)
theorem v2441_pb_checked : Scalar.distance (sourceCoefficient 29 64 1 1) v2441_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2441_pg : Scalar.QComplex := ((-93086377145737384106876 : Int)/10^30,(97325600760854658369 : Int)/10^30)
theorem v2441_pg_checked : Scalar.distance (sourceCoefficient 29 64 1 2) v2441_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2441_mb : Scalar.QComplex := ((-823472348177627635092991 : Int)/10^30,(-431476717846592549834641463 : Int)/10^30)
theorem v2441_mb_checked : Scalar.distance (sourceCoefficient 29 64 3 1) v2441_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2441_mg : Scalar.QComplex := ((-93086258497814840870596 : Int)/10^30,(177654915544061451400 : Int)/10^30)
theorem v2441_mg_checked : Scalar.distance (sourceCoefficient 29 64 3 2) v2441_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2441_upper : Scalar.QComplex := ((999996159533497487261282904420 : Int)/10^30,(-2771446960676411810404246143 : Int)/10^30)
theorem v2441_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 64 5) 1) 14) v2441_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2441 : Material (29 : Basis) (64 : Basis) where
  plus := ![v2441_pa,v2441_pb,v2441_pg]
  minus := ![(Primitive.Addresses.material2441 1).one,v2441_mb,v2441_mg]
  upper := v2441_upper
  lower := (Primitive.Addresses.material2441 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2441_pa_checked.trans (by decide +kernel)
    · exact v2441_pb_checked.trans (by decide +kernel)
    · exact v2441_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 64 Primitive.Addresses.material2441
    · exact v2441_mb_checked.trans (by decide +kernel)
    · exact v2441_mg_checked.trans (by decide +kernel)
  upper_error := v2441_upper_checked
  lower_error := reuse_lower_error 29 64 Primitive.Addresses.material2441

def v2442_pa : Scalar.QComplex := ((999999415171372419644308013663 : Int)/10^30,(-1081506779052349605035420719 : Int)/10^30)
theorem v2442_pa_checked : Scalar.distance (sourceCoefficient 29 65 1 0) v2442_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2442_pb : Scalar.QComplex := ((-466645842349817021696546 : Int)/10^30,(-431477248668620514143314764 : Int)/10^30)
theorem v2442_pb_checked : Scalar.distance (sourceCoefficient 29 65 1 1) v2442_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2442_pg : Scalar.QComplex := ((-93086373300882640254147 : Int)/10^30,(100673602639107081994 : Int)/10^30)
theorem v2442_pg_checked : Scalar.distance (sourceCoefficient 29 65 1 2) v2442_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2442_mb : Scalar.QComplex := ((-838991101183370000143127 : Int)/10^30,(-431476685315576351050988724 : Int)/10^30)
theorem v2442_mb_checked : Scalar.distance (sourceCoefficient 29 65 3 1) v2442_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2442_mg : Scalar.QComplex := ((-93086251763786696108233 : Int)/10^30,(181002912857763286392 : Int)/10^30)
theorem v2442_mg_checked : Scalar.distance (sourceCoefficient 29 65 3 2) v2442_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2442_upper : Scalar.QComplex := ((999996059207124589100299975842 : Int)/10^30,(-2807413439622549165861192295 : Int)/10^30)
theorem v2442_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 65 5) 1) 14) v2442_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2442 : Material (29 : Basis) (65 : Basis) where
  plus := ![v2442_pa,v2442_pb,v2442_pg]
  minus := ![(Primitive.Addresses.material2442 1).one,v2442_mb,v2442_mg]
  upper := v2442_upper
  lower := (Primitive.Addresses.material2442 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2442_pa_checked.trans (by decide +kernel)
    · exact v2442_pb_checked.trans (by decide +kernel)
    · exact v2442_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 65 Primitive.Addresses.material2442
    · exact v2442_mb_checked.trans (by decide +kernel)
    · exact v2442_mg_checked.trans (by decide +kernel)
  upper_error := v2442_upper_checked
  lower_error := reuse_lower_error 29 65 Primitive.Addresses.material2442

def v2443_pa : Scalar.QComplex := ((999999395995638844717786379261 : Int)/10^30,(-1099094335118371962870173687 : Int)/10^30)
theorem v2443_pa_checked : Scalar.distance (sourceCoefficient 29 66 1 0) v2443_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2443_pb : Scalar.QComplex := ((-474234475599711941431050 : Int)/10^30,(-431477239038763366292800289 : Int)/10^30)
theorem v2443_pb_checked : Scalar.distance (sourceCoefficient 29 66 1 1) v2443_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2443_pg : Scalar.QComplex := ((-93086371369615579857804 : Int)/10^30,(102310765245217892691 : Int)/10^30)
theorem v2443_pg_checked : Scalar.distance (sourceCoefficient 29 66 1 2) v2443_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2443_mb : Scalar.QComplex := ((-846579723297536937339866 : Int)/10^30,(-431476669137074073531210140 : Int)/10^30)
theorem v2443_mb_checked : Scalar.distance (sourceCoefficient 29 66 3 1) v2443_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2443_mg : Scalar.QComplex := ((-93086248419722760803855 : Int)/10^30,(182640073187687144724 : Int)/10^30)
theorem v2443_mg_checked : Scalar.distance (sourceCoefficient 29 66 3 2) v2443_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2443_upper : Scalar.QComplex := ((999996009676893334844516979793 : Int)/10^30,(-2825000936398396201455961593 : Int)/10^30)
theorem v2443_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 66 5) 1) 14) v2443_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2443 : Material (29 : Basis) (66 : Basis) where
  plus := ![v2443_pa,v2443_pb,v2443_pg]
  minus := ![(Primitive.Addresses.material2443 1).one,v2443_mb,v2443_mg]
  upper := v2443_upper
  lower := (Primitive.Addresses.material2443 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2443_pa_checked.trans (by decide +kernel)
    · exact v2443_pb_checked.trans (by decide +kernel)
    · exact v2443_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 66 Primitive.Addresses.material2443
    · exact v2443_mb_checked.trans (by decide +kernel)
    · exact v2443_mg_checked.trans (by decide +kernel)
  upper_error := v2443_upper_checked
  lower_error := reuse_lower_error 29 66 Primitive.Addresses.material2443

def v2444_pa : Scalar.QComplex := ((999999363117870046258189784823 : Int)/10^30,(-1128611471804462993256393491 : Int)/10^30)
theorem v2444_pa_checked : Scalar.distance (sourceCoefficient 29 67 1 0) v2444_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2444_pb : Scalar.QComplex := ((-486970453252711455480089 : Int)/10^30,(-431477222477056061605732846 : Int)/10^30)
theorem v2444_pb_checked : Scalar.distance (sourceCoefficient 29 67 1 1) v2444_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2444_pg : Scalar.QComplex := ((-93086368052877333362313 : Int)/10^30,(105058409762913610621 : Int)/10^30)
theorem v2444_pg_checked : Scalar.distance (sourceCoefficient 29 67 1 2) v2444_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2444_mb : Scalar.QComplex := ((-859315681916342415906474 : Int)/10^30,(-431476641584797828126292177 : Int)/10^30)
theorem v2444_mb_checked : Scalar.distance (sourceCoefficient 29 67 3 1) v2444_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2444_mg : Scalar.QComplex := ((-93086242731892279825478 : Int)/10^30,(185387713820113508778 : Int)/10^30)
theorem v2444_mg_checked : Scalar.distance (sourceCoefficient 29 67 3 2) v2444_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2444_upper : Scalar.QComplex := ((999995925855273357488875007069 : Int)/10^30,(-2854517972378133166096103801 : Int)/10^30)
theorem v2444_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 67 5) 1) 14) v2444_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2444 : Material (29 : Basis) (67 : Basis) where
  plus := ![v2444_pa,v2444_pb,v2444_pg]
  minus := ![(Primitive.Addresses.material2444 1).one,v2444_mb,v2444_mg]
  upper := v2444_upper
  lower := (Primitive.Addresses.material2444 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2444_pa_checked.trans (by decide +kernel)
    · exact v2444_pb_checked.trans (by decide +kernel)
    · exact v2444_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 67 Primitive.Addresses.material2444
    · exact v2444_mb_checked.trans (by decide +kernel)
    · exact v2444_mg_checked.trans (by decide +kernel)
  upper_error := v2444_upper_checked
  lower_error := reuse_lower_error 29 67 Primitive.Addresses.material2444

def v2445_pa : Scalar.QComplex := ((999999306429353569544204427405 : Int)/10^30,(-1177769422179345765504472761 : Int)/10^30)
theorem v2445_pa_checked : Scalar.distance (sourceCoefficient 29 68 1 0) v2445_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2445_pb : Scalar.QComplex := ((-508180997664357173031393 : Int)/10^30,(-431477193782630325133856411 : Int)/10^30)
theorem v2445_pb_checked : Scalar.distance (sourceCoefficient 29 68 1 1) v2445_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2445_pg : Scalar.QComplex := ((-93086362319161459766072 : Int)/10^30,(109634347200581075790 : Int)/10^30)
theorem v2445_pg_checked : Scalar.distance (sourceCoefficient 29 68 1 2) v2445_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2445_mb : Scalar.QComplex := ((-880526193668336017620320 : Int)/10^30,(-431476594586638236108626391 : Int)/10^30)
theorem v2445_mb_checked : Scalar.distance (sourceCoefficient 29 68 3 1) v2445_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2445_mg : Scalar.QComplex := ((-93086233049350625018354 : Int)/10^30,(189963644606011773294 : Int)/10^30)
theorem v2445_mg_checked : Scalar.distance (sourceCoefficient 29 68 3 2) v2445_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2445_upper : Scalar.QComplex := ((999995784324678539035141635044 : Int)/10^30,(-2903675751698786656677254827 : Int)/10^30)
theorem v2445_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 68 5) 1) 14) v2445_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2445 : Material (29 : Basis) (68 : Basis) where
  plus := ![v2445_pa,v2445_pb,v2445_pg]
  minus := ![(Primitive.Addresses.material2445 1).one,v2445_mb,v2445_mg]
  upper := v2445_upper
  lower := (Primitive.Addresses.material2445 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2445_pa_checked.trans (by decide +kernel)
    · exact v2445_pb_checked.trans (by decide +kernel)
    · exact v2445_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 68 Primitive.Addresses.material2445
    · exact v2445_mb_checked.trans (by decide +kernel)
    · exact v2445_mg_checked.trans (by decide +kernel)
  upper_error := v2445_upper_checked
  lower_error := reuse_lower_error 29 68 Primitive.Addresses.material2445

def v2446_pa : Scalar.QComplex := ((999999280713810581374395792362 : Int)/10^30,(-1199404794664682387290225139 : Int)/10^30)
theorem v2446_pa_checked : Scalar.distance (sourceCoefficient 29 69 1 0) v2446_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2446_pb : Scalar.QComplex := ((-517516171577896329564263 : Int)/10^30,(-431477180713074613778768695 : Int)/10^30)
theorem v2446_pb_checked : Scalar.distance (sourceCoefficient 29 69 1 1) v2446_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2446_pg : Scalar.QComplex := ((-93086359712472473730219 : Int)/10^30,(111648306464105721992 : Int)/10^30)
theorem v2446_pg_checked : Scalar.distance (sourceCoefficient 29 69 1 2) v2446_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2446_mb : Scalar.QComplex := ((-889861352827525339657135 : Int)/10^30,(-431476573461252744387722273 : Int)/10^30)
theorem v2446_mb_checked : Scalar.distance (sourceCoefficient 29 69 3 1) v2446_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2446_mg : Scalar.QComplex := ((-93086228704706470508260 : Int)/10^30,(191977600870192149166 : Int)/10^30)
theorem v2446_mg_checked : Scalar.distance (sourceCoefficient 29 69 3 2) v2446_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2446_upper : Scalar.QComplex := ((999995721268483687114586847449 : Int)/10^30,(-2925311047578083129189938343 : Int)/10^30)
theorem v2446_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 69 5) 1) 14) v2446_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2446 : Material (29 : Basis) (69 : Basis) where
  plus := ![v2446_pa,v2446_pb,v2446_pg]
  minus := ![(Primitive.Addresses.material2446 1).one,v2446_mb,v2446_mg]
  upper := v2446_upper
  lower := (Primitive.Addresses.material2446 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2446_pa_checked.trans (by decide +kernel)
    · exact v2446_pb_checked.trans (by decide +kernel)
    · exact v2446_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 69 Primitive.Addresses.material2446
    · exact v2446_mb_checked.trans (by decide +kernel)
    · exact v2446_mg_checked.trans (by decide +kernel)
  upper_error := v2446_upper_checked
  lower_error := reuse_lower_error 29 69 Primitive.Addresses.material2446

def v2447_pa : Scalar.QComplex := ((999999263542647769138664875192 : Int)/10^30,(-1213636750470374893944751196 : Int)/10^30)
theorem v2447_pa_checked : Scalar.distance (sourceCoefficient 29 70 1 0) v2447_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2447_pb : Scalar.QComplex := ((-523656938541557944308842 : Int)/10^30,(-431477171968959805864247326 : Int)/10^30)
theorem v2447_pb_checked : Scalar.distance (sourceCoefficient 29 70 1 1) v2447_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2447_pg : Scalar.QComplex := ((-93086357970049062276149 : Int)/10^30,(112973108199768565131 : Int)/10^30)
theorem v2447_pg_checked : Scalar.distance (sourceCoefficient 29 70 1 2) v2447_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2447_mb : Scalar.QComplex := ((-896002109958921507997435 : Int)/10^30,(-431476559417935872544083036 : Int)/10^30)
theorem v2447_mb_checked : Scalar.distance (sourceCoefficient 29 70 3 1) v2447_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2447_mg : Scalar.QComplex := ((-93086225819039476816262 : Int)/10^30,(193302400608937831440 : Int)/10^30)
theorem v2447_mg_checked : Scalar.distance (sourceCoefficient 29 70 3 2) v2447_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2447_upper : Scalar.QComplex := ((999995679534281841628603374522 : Int)/10^30,(-2939542952551080008035100113 : Int)/10^30)
theorem v2447_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 70 5) 1) 14) v2447_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2447 : Material (29 : Basis) (70 : Basis) where
  plus := ![v2447_pa,v2447_pb,v2447_pg]
  minus := ![(Primitive.Addresses.material2447 1).one,v2447_mb,v2447_mg]
  upper := v2447_upper
  lower := (Primitive.Addresses.material2447 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2447_pa_checked.trans (by decide +kernel)
    · exact v2447_pb_checked.trans (by decide +kernel)
    · exact v2447_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 70 Primitive.Addresses.material2447
    · exact v2447_mb_checked.trans (by decide +kernel)
    · exact v2447_mg_checked.trans (by decide +kernel)
  upper_error := v2447_upper_checked
  lower_error := reuse_lower_error 29 70 Primitive.Addresses.material2447

def v2448_pa : Scalar.QComplex := ((999999233764922636636597408274 : Int)/10^30,(-1237929548726636148851321067 : Int)/10^30)
theorem v2448_pa_checked : Scalar.distance (sourceCoefficient 29 71 1 0) v2448_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2448_pb : Scalar.QComplex := ((-534138731247239326311187 : Int)/10^30,(-431477156774256402835475226 : Int)/10^30)
theorem v2448_pb_checked : Scalar.distance (sourceCoefficient 29 71 1 1) v2448_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2448_pg : Scalar.QComplex := ((-93086354945054683851270 : Int)/10^30,(115234437666407280326 : Int)/10^30)
theorem v2448_pg_checked : Scalar.distance (sourceCoefficient 29 71 1 2) v2448_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2448_mb : Scalar.QComplex := ((-906483885649407731306215 : Int)/10^30,(-431476535177923104613728218 : Int)/10^30)
theorem v2448_mb_checked : Scalar.distance (sourceCoefficient 29 71 3 1) v2448_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2448_mg : Scalar.QComplex := ((-93086220842620741524286 : Int)/10^30,(195563726623146330451 : Int)/10^30)
theorem v2448_mg_checked : Scalar.distance (sourceCoefficient 29 71 3 2) v2448_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2448_upper : Scalar.QComplex := ((999995607829435094685725904560 : Int)/10^30,(-2963835663232419728203627049 : Int)/10^30)
theorem v2448_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 71 5) 1) 14) v2448_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2448 : Material (29 : Basis) (71 : Basis) where
  plus := ![v2448_pa,v2448_pb,v2448_pg]
  minus := ![(Primitive.Addresses.material2448 1).one,v2448_mb,v2448_mg]
  upper := v2448_upper
  lower := (Primitive.Addresses.material2448 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2448_pa_checked.trans (by decide +kernel)
    · exact v2448_pb_checked.trans (by decide +kernel)
    · exact v2448_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 71 Primitive.Addresses.material2448
    · exact v2448_mb_checked.trans (by decide +kernel)
    · exact v2448_mg_checked.trans (by decide +kernel)
  upper_error := v2448_upper_checked
  lower_error := reuse_lower_error 29 71 Primitive.Addresses.material2448

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
