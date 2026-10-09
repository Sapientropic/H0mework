import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B060

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1441_pa : Scalar.QComplex := ((999999952079161546083636695277 : Int)/10^30,(-309583065769796214289872075 : Int)/10^30)
theorem v1441_pa_checked : Scalar.distance (sourceCoefficient 16 26 1 0) v1441_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1441_pb : Scalar.QComplex := ((-133578132928947559412072 : Int)/10^30,(-431477497632571362129867836 : Int)/10^30)
theorem v1441_pb_checked : Scalar.distance (sourceCoefficient 16 26 1 1) v1441_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1441_pg : Scalar.QComplex := ((-93086425145885602072319 : Int)/10^30,(28817982259195786919 : Int)/10^30)
theorem v1441_pg_checked : Scalar.distance (sourceCoefficient 16 26 1 2) v1441_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1441_mb : Scalar.QComplex := ((-505923730623507363257653 : Int)/10^30,(-431477221701866915814801937 : Int)/10^30)
theorem v1441_mb_checked : Scalar.distance (sourceCoefficient 16 26 3 1) v1441_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1441_mg : Scalar.QComplex := ((-93086365616934484519411 : Int)/10^30,(109147363972885966635 : Int)/10^30)
theorem v1441_mg_checked : Scalar.distance (sourceCoefficient 16 26 3 2) v1441_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1441_upper : Scalar.QComplex := ((999997928384414807907127022074 : Int)/10^30,(-2035491802683826318527916430 : Int)/10^30)
theorem v1441_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 26 5) 1) 14) v1441_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1441 : Material (16 : Basis) (26 : Basis) where
  plus := ![v1441_pa,v1441_pb,v1441_pg]
  minus := ![(Primitive.Addresses.material1441 1).one,v1441_mb,v1441_mg]
  upper := v1441_upper
  lower := (Primitive.Addresses.material1441 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1441_pa_checked.trans (by decide +kernel)
    · exact v1441_pb_checked.trans (by decide +kernel)
    · exact v1441_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 26 Primitive.Addresses.material1441
    · exact v1441_mb_checked.trans (by decide +kernel)
    · exact v1441_mg_checked.trans (by decide +kernel)
  upper_error := v1441_upper_checked
  lower_error := reuse_lower_error 16 26 Primitive.Addresses.material1441

def v1442_pa : Scalar.QComplex := ((999999950504515507885596299966 : Int)/10^30,(-314628299004437651189970677 : Int)/10^30)
theorem v1442_pa_checked : Scalar.distance (sourceCoefficient 16 27 1 0) v1442_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1442_pb : Scalar.QComplex := ((-135755037599579805292978 : Int)/10^30,(-431477496810939121624909308 : Int)/10^30)
theorem v1442_pb_checked : Scalar.distance (sourceCoefficient 16 27 1 1) v1442_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1442_pg : Scalar.QComplex := ((-93086424983967548469934 : Int)/10^30,(29287625002715086264 : Int)/10^30)
theorem v1442_pg_checked : Scalar.distance (sourceCoefficient 16 27 1 2) v1442_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1442_mb : Scalar.QComplex := ((-508100633774546892190492 : Int)/10^30,(-431477219001664294632244270 : Int)/10^30)
theorem v1442_mb_checked : Scalar.distance (sourceCoefficient 16 27 3 1) v1442_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1442_mg : Scalar.QComplex := ((-93086365049735955473334 : Int)/10^30,(109617006401807821094 : Int)/10^30)
theorem v1442_mg_checked : Scalar.distance (sourceCoefficient 16 27 3 2) v1442_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1442_upper : Scalar.QComplex := ((999997918102156251951960124382 : Int)/10^30,(-2040537025686489295999938307 : Int)/10^30)
theorem v1442_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 27 5) 1) 14) v1442_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1442 : Material (16 : Basis) (27 : Basis) where
  plus := ![v1442_pa,v1442_pb,v1442_pg]
  minus := ![(Primitive.Addresses.material1442 1).one,v1442_mb,v1442_mg]
  upper := v1442_upper
  lower := (Primitive.Addresses.material1442 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1442_pa_checked.trans (by decide +kernel)
    · exact v1442_pb_checked.trans (by decide +kernel)
    · exact v1442_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 27 Primitive.Addresses.material1442
    · exact v1442_mb_checked.trans (by decide +kernel)
    · exact v1442_mg_checked.trans (by decide +kernel)
  upper_error := v1442_upper_checked
  lower_error := reuse_lower_error 16 27 Primitive.Addresses.material1442

def v1443_pa : Scalar.QComplex := ((999999948343020891454161204923 : Int)/10^30,(-321424883213244999336190178 : Int)/10^30)
theorem v1443_pa_checked : Scalar.distance (sourceCoefficient 16 28 1 0) v1443_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1443_pb : Scalar.QComplex := ((-138687610822573376347612 : Int)/10^30,(-431477495680942483820519165 : Int)/10^30)
theorem v1443_pb_checked : Scalar.distance (sourceCoefficient 16 28 1 1) v1443_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1443_pg : Scalar.QComplex := ((-93086424761472597418628 : Int)/10^30,(29920294753286888112 : Int)/10^30)
theorem v1443_pg_checked : Scalar.distance (sourceCoefficient 16 28 1 2) v1443_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1443_mb : Scalar.QComplex := ((-511033204930473221841484 : Int)/10^30,(-431477215340989464328784526 : Int)/10^30)
theorem v1443_mb_checked : Scalar.distance (sourceCoefficient 16 28 3 1) v1443_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1443_mg : Scalar.QComplex := ((-93086364281275586911407 : Int)/10^30,(110249675724804638411 : Int)/10^30)
theorem v1443_mg_checked : Scalar.distance (sourceCoefficient 16 28 3 2) v1443_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1443_upper : Scalar.QComplex := ((999997904210377091714320493953 : Int)/10^30,(-2047333596042039229291297067 : Int)/10^30)
theorem v1443_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 28 5) 1) 14) v1443_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1443 : Material (16 : Basis) (28 : Basis) where
  plus := ![v1443_pa,v1443_pb,v1443_pg]
  minus := ![(Primitive.Addresses.material1443 1).one,v1443_mb,v1443_mg]
  upper := v1443_upper
  lower := (Primitive.Addresses.material1443 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1443_pa_checked.trans (by decide +kernel)
    · exact v1443_pb_checked.trans (by decide +kernel)
    · exact v1443_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 28 Primitive.Addresses.material1443
    · exact v1443_mb_checked.trans (by decide +kernel)
    · exact v1443_mg_checked.trans (by decide +kernel)
  upper_error := v1443_upper_checked
  lower_error := reuse_lower_error 16 28 Primitive.Addresses.material1443

def v1444_pa : Scalar.QComplex := ((999999943823750050724094610629 : Int)/10^30,(-335190239629349518467243101 : Int)/10^30)
theorem v1444_pa_checked : Scalar.distance (sourceCoefficient 16 29 1 0) v1444_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1444_pb : Scalar.QComplex := ((-144627052502158307985609 : Int)/10^30,(-431477493310903676263210838 : Int)/10^30)
theorem v1444_pb_checked : Scalar.distance (sourceCoefficient 16 29 1 1) v1444_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1444_pg : Scalar.QComplex := ((-93086424295476574382797 : Int)/10^30,(31201662618632493990 : Int)/10^30)
theorem v1444_pg_checked : Scalar.distance (sourceCoefficient 16 29 1 2) v1444_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1444_mb : Scalar.QComplex := ((-516972642353295821939019 : Int)/10^30,(-431477207845480872286532450 : Int)/10^30)
theorem v1444_mb_checked : Scalar.distance (sourceCoefficient 16 29 3 1) v1444_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1444_mg : Scalar.QComplex := ((-93086362709516980260269 : Int)/10^30,(111531042710904846419 : Int)/10^30)
theorem v1444_mg_checked : Scalar.distance (sourceCoefficient 16 29 3 2) v1444_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1444_upper : Scalar.QComplex := ((999997875933356591090008883215 : Int)/10^30,(-2061098924156410872934770538 : Int)/10^30)
theorem v1444_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 29 5) 1) 14) v1444_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1444 : Material (16 : Basis) (29 : Basis) where
  plus := ![v1444_pa,v1444_pb,v1444_pg]
  minus := ![(Primitive.Addresses.material1444 1).one,v1444_mb,v1444_mg]
  upper := v1444_upper
  lower := (Primitive.Addresses.material1444 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1444_pa_checked.trans (by decide +kernel)
    · exact v1444_pb_checked.trans (by decide +kernel)
    · exact v1444_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 29 Primitive.Addresses.material1444
    · exact v1444_mb_checked.trans (by decide +kernel)
    · exact v1444_mg_checked.trans (by decide +kernel)
  upper_error := v1444_upper_checked
  lower_error := reuse_lower_error 16 29 Primitive.Addresses.material1444

def v1445_pa : Scalar.QComplex := ((999999942061693124346297789268 : Int)/10^30,(-340406536944371855292761461 : Int)/10^30)
theorem v1445_pa_checked : Scalar.distance (sourceCoefficient 16 30 1 0) v1445_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1445_pb : Scalar.QComplex := ((-146877767461833877860781 : Int)/10^30,(-431477492384310486465237545 : Int)/10^30)
theorem v1445_pb_checked : Scalar.distance (sourceCoefficient 16 30 1 1) v1445_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1445_pg : Scalar.QComplex := ((-93086424113513742464954 : Int)/10^30,(31687229104920686824 : Int)/10^30)
theorem v1445_pg_checked : Scalar.distance (sourceCoefficient 16 30 1 2) v1445_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1445_mb : Scalar.QComplex := ((-519223355675319158984242 : Int)/10^30,(-431477204976622385740344777 : Int)/10^30)
theorem v1445_mb_checked : Scalar.distance (sourceCoefficient 16 30 3 1) v1445_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1445_mg : Scalar.QComplex := ((-93086362108532207531517 : Int)/10^30,(112016608859368716279 : Int)/10^30)
theorem v1445_mg_checked : Scalar.distance (sourceCoefficient 16 30 3 2) v1445_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1445_upper : Scalar.QComplex := ((999997865168446342156301250026 : Int)/10^30,(-2066315210661220705988017262 : Int)/10^30)
theorem v1445_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 30 5) 1) 14) v1445_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1445 : Material (16 : Basis) (30 : Basis) where
  plus := ![v1445_pa,v1445_pb,v1445_pg]
  minus := ![(Primitive.Addresses.material1445 1).one,v1445_mb,v1445_mg]
  upper := v1445_upper
  lower := (Primitive.Addresses.material1445 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1445_pa_checked.trans (by decide +kernel)
    · exact v1445_pb_checked.trans (by decide +kernel)
    · exact v1445_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 30 Primitive.Addresses.material1445
    · exact v1445_mb_checked.trans (by decide +kernel)
    · exact v1445_mg_checked.trans (by decide +kernel)
  upper_error := v1445_upper_checked
  lower_error := reuse_lower_error 16 30 Primitive.Addresses.material1445

def v1446_pa : Scalar.QComplex := ((999999938223308662784243606257 : Int)/10^30,(-351501605768838444738743817 : Int)/10^30)
theorem v1446_pa_checked : Scalar.distance (sourceCoefficient 16 31 1 0) v1446_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1446_pb : Scalar.QComplex := ((-151665040084500764276091 : Int)/10^30,(-431477490361388004758062325 : Int)/10^30)
theorem v1446_pb_checked : Scalar.distance (sourceCoefficient 16 31 1 1) v1446_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1446_pg : Scalar.QComplex := ((-93086423716651585161962 : Int)/10^30,(32720029433016677475 : Int)/10^30)
theorem v1446_pg_checked : Scalar.distance (sourceCoefficient 16 31 1 2) v1446_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1446_mb : Scalar.QComplex := ((-524010624769774666146567 : Int)/10^30,(-431477198822499994653216108 : Int)/10^30)
theorem v1446_mb_checked : Scalar.distance (sourceCoefficient 16 31 3 1) v1446_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1446_mg : Scalar.QComplex := ((-93086360820410030451641 : Int)/10^30,(113049408460431775729 : Int)/10^30)
theorem v1446_mg_checked : Scalar.distance (sourceCoefficient 16 31 3 2) v1446_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1446_upper : Scalar.QComplex := ((999997842180985343168802631465 : Int)/10^30,(-2077410256336182234590393268 : Int)/10^30)
theorem v1446_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 31 5) 1) 14) v1446_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1446 : Material (16 : Basis) (31 : Basis) where
  plus := ![v1446_pa,v1446_pb,v1446_pg]
  minus := ![(Primitive.Addresses.material1446 1).one,v1446_mb,v1446_mg]
  upper := v1446_upper
  lower := (Primitive.Addresses.material1446 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1446_pa_checked.trans (by decide +kernel)
    · exact v1446_pb_checked.trans (by decide +kernel)
    · exact v1446_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 31 Primitive.Addresses.material1446
    · exact v1446_mb_checked.trans (by decide +kernel)
    · exact v1446_mg_checked.trans (by decide +kernel)
  upper_error := v1446_upper_checked
  lower_error := reuse_lower_error 16 31 Primitive.Addresses.material1446

def v1447_pa : Scalar.QComplex := ((999999936533099817516151051602 : Int)/10^30,(-356277695536670214276833945 : Int)/10^30)
theorem v1447_pa_checked : Scalar.distance (sourceCoefficient 16 32 1 0) v1447_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1447_pb : Scalar.QComplex := ((-153725815380384665544570 : Int)/10^30,(-431477489468776788280043045 : Int)/10^30)
theorem v1447_pb_checked : Scalar.distance (sourceCoefficient 16 32 1 1) v1447_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1447_pg : Scalar.QComplex := ((-93086423541698408492348 : Int)/10^30,(33164618570042292606 : Int)/10^30)
theorem v1447_pg_checked : Scalar.distance (sourceCoefficient 16 32 1 2) v1447_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1447_mb : Scalar.QComplex := ((-526071398528054464570059 : Int)/10^30,(-431477196151532844061253934 : Int)/10^30)
theorem v1447_mb_checked : Scalar.distance (sourceCoefficient 16 32 3 1) v1447_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1447_mg : Scalar.QComplex := ((-93086360261796517223407 : Int)/10^30,(113493997280939824551 : Int)/10^30)
theorem v1447_mg_checked : Scalar.distance (sourceCoefficient 16 32 3 2) v1447_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1447_upper : Scalar.QComplex := ((999997832247681359469717904903 : Int)/10^30,(-2082186336073442201473957650 : Int)/10^30)
theorem v1447_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 32 5) 1) 14) v1447_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1447 : Material (16 : Basis) (32 : Basis) where
  plus := ![v1447_pa,v1447_pb,v1447_pg]
  minus := ![(Primitive.Addresses.material1447 1).one,v1447_mb,v1447_mg]
  upper := v1447_upper
  lower := (Primitive.Addresses.material1447 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1447_pa_checked.trans (by decide +kernel)
    · exact v1447_pb_checked.trans (by decide +kernel)
    · exact v1447_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 32 Primitive.Addresses.material1447
    · exact v1447_mb_checked.trans (by decide +kernel)
    · exact v1447_mg_checked.trans (by decide +kernel)
  upper_error := v1447_upper_checked
  lower_error := reuse_lower_error 16 32 Primitive.Addresses.material1447

def v1448_pa : Scalar.QComplex := ((999999934139521632275297476345 : Int)/10^30,(-362933812695712872486182596 : Int)/10^30)
theorem v1448_pa_checked : Scalar.distance (sourceCoefficient 16 33 1 0) v1448_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1448_pb : Scalar.QComplex := ((-156597780199458339436452 : Int)/10^30,(-431477488202915581327938467 : Int)/10^30)
theorem v1448_pb_checked : Scalar.distance (sourceCoefficient 16 33 1 1) v1448_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1448_pg : Scalar.QComplex := ((-93086423293745914473010 : Int)/10^30,(33784212741250635854 : Int)/10^30)
theorem v1448_pg_checked : Scalar.distance (sourceCoefficient 16 33 1 2) v1448_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1448_mb : Scalar.QComplex := ((-528943361185383171717138 : Int)/10^30,(-431477192407295818080358136 : Int)/10^30)
theorem v1448_mb_checked : Scalar.distance (sourceCoefficient 16 33 3 1) v1448_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1448_mg : Scalar.QComplex := ((-93086359479162251260885 : Int)/10^30,(114113591007473106033 : Int)/10^30)
theorem v1448_mg_checked : Scalar.distance (sourceCoefficient 16 33 3 2) v1448_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1448_upper : Scalar.QComplex := ((999997818366252360906516672702 : Int)/10^30,(-2088842439187881429726032363 : Int)/10^30)
theorem v1448_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 33 5) 1) 14) v1448_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1448 : Material (16 : Basis) (33 : Basis) where
  plus := ![v1448_pa,v1448_pb,v1448_pg]
  minus := ![(Primitive.Addresses.material1448 1).one,v1448_mb,v1448_mg]
  upper := v1448_upper
  lower := (Primitive.Addresses.material1448 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1448_pa_checked.trans (by decide +kernel)
    · exact v1448_pb_checked.trans (by decide +kernel)
    · exact v1448_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 33 Primitive.Addresses.material1448
    · exact v1448_mb_checked.trans (by decide +kernel)
    · exact v1448_mg_checked.trans (by decide +kernel)
  upper_error := v1448_upper_checked
  lower_error := reuse_lower_error 16 33 Primitive.Addresses.material1448

def v1449_pa : Scalar.QComplex := ((999999928141297930833380189335 : Int)/10^30,(-379100776805667039714762786 : Int)/10^30)
theorem v1449_pa_checked : Scalar.distance (sourceCoefficient 16 34 1 0) v1449_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1449_pb : Scalar.QComplex := ((-163573461500226453654126 : Int)/10^30,(-431477485022142579907819459 : Int)/10^30)
theorem v1449_pb_checked : Scalar.distance (sourceCoefficient 16 34 1 1) v1449_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1449_pg : Scalar.QComplex := ((-93086422671461271535218 : Int)/10^30,(35289137680643254555 : Int)/10^30)
theorem v1449_pg_checked : Scalar.distance (sourceCoefficient 16 34 1 2) v1449_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1449_mb : Scalar.QComplex := ((-535919037143922489746625 : Int)/10^30,(-431477183206825211467649263 : Int)/10^30)
theorem v1449_mb_checked : Scalar.distance (sourceCoefficient 16 34 3 1) v1449_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1449_mg : Scalar.QComplex := ((-93086357558195396635460 : Int)/10^30,(115618514849509771136 : Int)/10^30)
theorem v1449_mg_checked : Scalar.distance (sourceCoefficient 16 34 3 2) v1449_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1449_upper : Scalar.QComplex := ((999997784465324194860479994586 : Int)/10^30,(-2105009368866651706101829563 : Int)/10^30)
theorem v1449_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 34 5) 1) 14) v1449_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1449 : Material (16 : Basis) (34 : Basis) where
  plus := ![v1449_pa,v1449_pb,v1449_pg]
  minus := ![(Primitive.Addresses.material1449 1).one,v1449_mb,v1449_mg]
  upper := v1449_upper
  lower := (Primitive.Addresses.material1449 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1449_pa_checked.trans (by decide +kernel)
    · exact v1449_pb_checked.trans (by decide +kernel)
    · exact v1449_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 34 Primitive.Addresses.material1449
    · exact v1449_mb_checked.trans (by decide +kernel)
    · exact v1449_mg_checked.trans (by decide +kernel)
  upper_error := v1449_upper_checked
  lower_error := reuse_lower_error 16 34 Primitive.Addresses.material1449

def v1450_pa : Scalar.QComplex := ((999999907350851604759259015944 : Int)/10^30,(-430462876688126015228377282 : Int)/10^30)
theorem v1450_pa_checked : Scalar.distance (sourceCoefficient 16 35 1 0) v1450_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1450_pb : Scalar.QComplex := ((-185735051857576272022902 : Int)/10^30,(-431477473919193476474757656 : Int)/10^30)
theorem v1450_pb_checked : Scalar.distance (sourceCoefficient 16 35 1 1) v1450_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1450_pg : Scalar.QComplex := ((-93086420506138766323216 : Int)/10^30,(40070252064147786347 : Int)/10^30)
theorem v1450_pg_checked : Scalar.distance (sourceCoefficient 16 35 1 2) v1450_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1450_mb : Scalar.QComplex := ((-558080609668154365361533 : Int)/10^30,(-431477152979425884754777958 : Int)/10^30)
theorem v1450_mb_checked : Scalar.distance (sourceCoefficient 16 35 3 1) v1450_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1450_mg : Scalar.QComplex := ((-93086351266987318105857 : Int)/10^30,(120399625584211110734 : Int)/10^30)
theorem v1450_mg_checked : Scalar.distance (sourceCoefficient 16 35 3 2) v1450_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1450_upper : Scalar.QComplex := ((999997675028583969892812383846 : Int)/10^30,(-2156371356368872058522763191 : Int)/10^30)
theorem v1450_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 35 5) 1) 14) v1450_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1450 : Material (16 : Basis) (35 : Basis) where
  plus := ![v1450_pa,v1450_pb,v1450_pg]
  minus := ![(Primitive.Addresses.material1450 1).one,v1450_mb,v1450_mg]
  upper := v1450_upper
  lower := (Primitive.Addresses.material1450 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1450_pa_checked.trans (by decide +kernel)
    · exact v1450_pb_checked.trans (by decide +kernel)
    · exact v1450_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 35 Primitive.Addresses.material1450
    · exact v1450_mb_checked.trans (by decide +kernel)
    · exact v1450_mg_checked.trans (by decide +kernel)
  upper_error := v1450_upper_checked
  lower_error := reuse_lower_error 16 35 Primitive.Addresses.material1450

def v1451_pa : Scalar.QComplex := ((999999900270731755936487554625 : Int)/10^30,(-446607799464138423139080365 : Int)/10^30)
theorem v1451_pa_checked : Scalar.distance (sourceCoefficient 16 36 1 0) v1451_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1451_pb : Scalar.QComplex := ((-192701222664648728855542 : Int)/10^30,(-431477470115633896877532165 : Int)/10^30)
theorem v1451_pb_checked : Scalar.distance (sourceCoefficient 16 36 1 1) v1451_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1451_pg : Scalar.QComplex := ((-93086419766319593118316 : Int)/10^30,(41573125237888430493 : Int)/10^30)
theorem v1451_pg_checked : Scalar.distance (sourceCoefficient 16 36 1 2) v1451_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1451_mb : Scalar.QComplex := ((-565046774599102449759314 : Int)/10^30,(-431477143164376059579485288 : Int)/10^30)
theorem v1451_mb_checked : Scalar.distance (sourceCoefficient 16 36 3 1) v1451_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1451_mg : Scalar.QComplex := ((-93086349230256558326361 : Int)/10^30,(121902497559932761342 : Int)/10^30)
theorem v1451_mg_checked : Scalar.distance (sourceCoefficient 16 36 3 2) v1451_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1451_upper : Scalar.QComplex := ((999997640083802610632425808928 : Int)/10^30,(-2172516242879273951802409964 : Int)/10^30)
theorem v1451_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 36 5) 1) 14) v1451_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1451 : Material (16 : Basis) (36 : Basis) where
  plus := ![v1451_pa,v1451_pb,v1451_pg]
  minus := ![(Primitive.Addresses.material1451 1).one,v1451_mb,v1451_mg]
  upper := v1451_upper
  lower := (Primitive.Addresses.material1451 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1451_pa_checked.trans (by decide +kernel)
    · exact v1451_pb_checked.trans (by decide +kernel)
    · exact v1451_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 36 Primitive.Addresses.material1451
    · exact v1451_mb_checked.trans (by decide +kernel)
    · exact v1451_mg_checked.trans (by decide +kernel)
  upper_error := v1451_upper_checked
  lower_error := reuse_lower_error 16 36 Primitive.Addresses.material1451

def v1452_pa : Scalar.QComplex := ((999999897168028198839287468815 : Int)/10^30,(-453501855594778135134525672 : Int)/10^30)
theorem v1452_pa_checked : Scalar.distance (sourceCoefficient 16 37 1 0) v1452_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1452_pb : Scalar.QComplex := ((-195675852709234430777800 : Int)/10^30,(-431477468445784634726527878 : Int)/10^30)
theorem v1452_pb_checked : Scalar.distance (sourceCoefficient 16 37 1 1) v1452_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1452_pg : Scalar.QComplex := ((-93086419441784181335556 : Int)/10^30,(42214868288561103146 : Int)/10^30)
theorem v1452_pg_checked : Scalar.distance (sourceCoefficient 16 37 1 2) v1452_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1452_mb : Scalar.QComplex := ((-568021402095092732755971 : Int)/10^30,(-431477138927555663076136643 : Int)/10^30)
theorem v1452_mb_checked : Scalar.distance (sourceCoefficient 16 37 3 1) v1452_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1452_mg : Scalar.QComplex := ((-93086348351925917686521 : Int)/10^30,(122544240091595723288 : Int)/10^30)
theorem v1452_mg_checked : Scalar.distance (sourceCoefficient 16 37 3 2) v1452_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1452_upper : Scalar.QComplex := ((999997625082588217050190295969 : Int)/10^30,(-2179410283387042025448925034 : Int)/10^30)
theorem v1452_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 37 5) 1) 14) v1452_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1452 : Material (16 : Basis) (37 : Basis) where
  plus := ![v1452_pa,v1452_pb,v1452_pg]
  minus := ![(Primitive.Addresses.material1452 1).one,v1452_mb,v1452_mg]
  upper := v1452_upper
  lower := (Primitive.Addresses.material1452 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1452_pa_checked.trans (by decide +kernel)
    · exact v1452_pb_checked.trans (by decide +kernel)
    · exact v1452_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 37 Primitive.Addresses.material1452
    · exact v1452_mb_checked.trans (by decide +kernel)
    · exact v1452_mg_checked.trans (by decide +kernel)
  upper_error := v1452_upper_checked
  lower_error := reuse_lower_error 16 37 Primitive.Addresses.material1452

def v1453_pa : Scalar.QComplex := ((999999886329505556332312319899 : Int)/10^30,(-476802869083601538988773738 : Int)/10^30)
theorem v1453_pa_checked : Scalar.distance (sourceCoefficient 16 38 1 0) v1453_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1453_pb : Scalar.QComplex := ((-205729715497765061945555 : Int)/10^30,(-431477462599526429542575350 : Int)/10^30)
theorem v1453_pb_checked : Scalar.distance (sourceCoefficient 16 38 1 1) v1453_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1453_pg : Scalar.QComplex := ((-93086418306692214195611 : Int)/10^30,(44383876366484309363 : Int)/10^30)
theorem v1453_pg_checked : Scalar.distance (sourceCoefficient 16 38 1 2) v1453_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1453_mb : Scalar.QComplex := ((-578075256095053238146799 : Int)/10^30,(-431477124405268857390295284 : Int)/10^30)
theorem v1453_mb_checked : Scalar.distance (sourceCoefficient 16 38 3 1) v1453_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1453_mg : Scalar.QComplex := ((-93086345345078090442928 : Int)/10^30,(124713246382364848530 : Int)/10^30)
theorem v1453_mg_checked : Scalar.distance (sourceCoefficient 16 38 3 2) v1453_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1453_upper : Scalar.QComplex := ((999997574028646286971518661118 : Int)/10^30,(-2202711243465436149144217298 : Int)/10^30)
theorem v1453_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 38 5) 1) 14) v1453_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1453 : Material (16 : Basis) (38 : Basis) where
  plus := ![v1453_pa,v1453_pb,v1453_pg]
  minus := ![(Primitive.Addresses.material1453 1).one,v1453_mb,v1453_mg]
  upper := v1453_upper
  lower := (Primitive.Addresses.material1453 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1453_pa_checked.trans (by decide +kernel)
    · exact v1453_pb_checked.trans (by decide +kernel)
    · exact v1453_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 38 Primitive.Addresses.material1453
    · exact v1453_mb_checked.trans (by decide +kernel)
    · exact v1453_mg_checked.trans (by decide +kernel)
  upper_error := v1453_upper_checked
  lower_error := reuse_lower_error 16 38 Primitive.Addresses.material1453

def v1454_pa : Scalar.QComplex := ((999999879793013505746370221373 : Int)/10^30,(-490320261195463609945921314 : Int)/10^30)
theorem v1454_pa_checked : Scalar.distance (sourceCoefficient 16 39 1 0) v1454_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1454_pb : Scalar.QComplex := ((-211562165859873804290246 : Int)/10^30,(-431477459064832012557286458 : Int)/10^30)
theorem v1454_pb_checked : Scalar.distance (sourceCoefficient 16 39 1 1) v1454_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1454_pg : Scalar.QComplex := ((-93086417621177546166347 : Int)/10^30,(45642162088272542502 : Int)/10^30)
theorem v1454_pg_checked : Scalar.distance (sourceCoefficient 16 39 1 2) v1454_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1454_mb : Scalar.QComplex := ((-583907701235192069397293 : Int)/10^30,(-431477115837433777846464582 : Int)/10^30)
theorem v1454_mb_checked : Scalar.distance (sourceCoefficient 16 39 3 1) v1454_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1454_mg : Scalar.QComplex := ((-93086343573719770844038 : Int)/10^30,(125971531044067516874 : Int)/10^30)
theorem v1454_mg_checked : Scalar.distance (sourceCoefficient 16 39 3 2) v1454_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1454_upper : Scalar.QComplex := ((999997544162371474881871287796 : Int)/10^30,(-2216228604163338240517002533 : Int)/10^30)
theorem v1454_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 39 5) 1) 14) v1454_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1454 : Material (16 : Basis) (39 : Basis) where
  plus := ![v1454_pa,v1454_pb,v1454_pg]
  minus := ![(Primitive.Addresses.material1454 1).one,v1454_mb,v1454_mg]
  upper := v1454_upper
  lower := (Primitive.Addresses.material1454 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1454_pa_checked.trans (by decide +kernel)
    · exact v1454_pb_checked.trans (by decide +kernel)
    · exact v1454_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 39 Primitive.Addresses.material1454
    · exact v1454_mb_checked.trans (by decide +kernel)
    · exact v1454_mg_checked.trans (by decide +kernel)
  upper_error := v1454_upper_checked
  lower_error := reuse_lower_error 16 39 Primitive.Addresses.material1454

def v1455_pa : Scalar.QComplex := ((999999868386886452778438956707 : Int)/10^30,(-513055756982056936057759059 : Int)/10^30)
theorem v1455_pa_checked : Scalar.distance (sourceCoefficient 16 40 1 0) v1455_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1455_pb : Scalar.QComplex := ((-221372020344824635437272 : Int)/10^30,(-431477452882583701604839338 : Int)/10^30)
theorem v1455_pb_checked : Scalar.distance (sourceCoefficient 16 40 1 1) v1455_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1455_pg : Scalar.QComplex := ((-93086416423424398708187 : Int)/10^30,(47758528128515567316 : Int)/10^30)
theorem v1455_pg_checked : Scalar.distance (sourceCoefficient 16 40 1 2) v1455_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1455_mb : Scalar.QComplex := ((-593717546732483889074941 : Int)/10^30,(-431477101189725167759932505 : Int)/10^30)
theorem v1455_mb_checked : Scalar.distance (sourceCoefficient 16 40 3 1) v1455_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1455_mg : Scalar.QComplex := ((-93086340549638494222482 : Int)/10^30,(128087895262683720742 : Int)/10^30)
theorem v1455_mg_checked : Scalar.distance (sourceCoefficient 16 40 3 2) v1455_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1455_upper : Scalar.QComplex := ((999997493516858230406265187563 : Int)/10^30,(-2238964046402140753780070047 : Int)/10^30)
theorem v1455_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 40 5) 1) 14) v1455_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1455 : Material (16 : Basis) (40 : Basis) where
  plus := ![v1455_pa,v1455_pb,v1455_pg]
  minus := ![(Primitive.Addresses.material1455 1).one,v1455_mb,v1455_mg]
  upper := v1455_upper
  lower := (Primitive.Addresses.material1455 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1455_pa_checked.trans (by decide +kernel)
    · exact v1455_pb_checked.trans (by decide +kernel)
    · exact v1455_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 40 Primitive.Addresses.material1455
    · exact v1455_mb_checked.trans (by decide +kernel)
    · exact v1455_mg_checked.trans (by decide +kernel)
  upper_error := v1455_upper_checked
  lower_error := reuse_lower_error 16 40 Primitive.Addresses.material1455

def v1456_pa : Scalar.QComplex := ((999999860850896731226573380319 : Int)/10^30,(-527539749379204517147952145 : Int)/10^30)
theorem v1456_pa_checked : Scalar.distance (sourceCoefficient 16 41 1 0) v1456_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1456_pb : Scalar.QComplex := ((-227621536870270584668298 : Int)/10^30,(-431477448789019397440377173 : Int)/10^30)
theorem v1456_pb_checked : Scalar.distance (sourceCoefficient 16 41 1 1) v1456_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1456_pg : Scalar.QComplex := ((-93086415631104944542624 : Int)/10^30,(49106791205807529024 : Int)/10^30)
theorem v1456_pg_checked : Scalar.distance (sourceCoefficient 16 41 1 2) v1456_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1456_mb : Scalar.QComplex := ((-599967057398387591665754 : Int)/10^30,(-431477091703111094132422837 : Int)/10^30)
theorem v1456_mb_checked : Scalar.distance (sourceCoefficient 16 41 3 1) v1456_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1456_mg : Scalar.QComplex := ((-93086338593829022885538 : Int)/10^30,(129436157154219715907 : Int)/10^30)
theorem v1456_mg_checked : Scalar.distance (sourceCoefficient 16 41 3 2) v1456_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1456_upper : Scalar.QComplex := ((999997460982822832875165443141 : Int)/10^30,(-2253448004220648468831955334 : Int)/10^30)
theorem v1456_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 16 41 5) 1) 14) v1456_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1456 : Material (16 : Basis) (41 : Basis) where
  plus := ![v1456_pa,v1456_pb,v1456_pg]
  minus := ![(Primitive.Addresses.material1456 1).one,v1456_mb,v1456_mg]
  upper := v1456_upper
  lower := (Primitive.Addresses.material1456 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1456_pa_checked.trans (by decide +kernel)
    · exact v1456_pb_checked.trans (by decide +kernel)
    · exact v1456_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 16 41 Primitive.Addresses.material1456
    · exact v1456_mb_checked.trans (by decide +kernel)
    · exact v1456_mg_checked.trans (by decide +kernel)
  upper_error := v1456_upper_checked
  lower_error := reuse_lower_error 16 41 Primitive.Addresses.material1456

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
