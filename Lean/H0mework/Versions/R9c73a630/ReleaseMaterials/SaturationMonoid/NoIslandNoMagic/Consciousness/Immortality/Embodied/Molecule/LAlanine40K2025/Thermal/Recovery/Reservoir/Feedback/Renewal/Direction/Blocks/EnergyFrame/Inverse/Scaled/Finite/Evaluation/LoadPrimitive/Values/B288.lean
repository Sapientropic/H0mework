import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B192

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4609_pa : Scalar.QComplex := ((999997188087183277496374925977 : Int)/10^30,(-2371458986908970011813132127 : Int)/10^30)
theorem v4609_pa_checked : Scalar.distance (sourceCoefficient 80 90 1 0) v4609_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4609_pb : Scalar.QComplex := ((-1023231235524925280641553 : Int)/10^30,(-431476303801317614833934692 : Int)/10^30)
theorem v4609_pb_checked : Scalar.distance (sourceCoefficient 80 90 1 1) v4609_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4609_pg : Scalar.QComplex := ((-93086167722969383922282 : Int)/10^30,(220750649735132729120 : Int)/10^30)
theorem v4609_pg_checked : Scalar.distance (sourceCoefficient 80 90 1 2) v4609_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4609_mb : Scalar.QComplex := ((-1395575471738372012397293 : Int)/10^30,(-431475260140498634455368799 : Int)/10^30)
theorem v4609_mb_checked : Scalar.distance (sourceCoefficient 80 90 3 1) v4609_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4609_mg : Scalar.QComplex := ((-93085942564866411402944 : Int)/10^30,(301079737839136252806 : Int)/10^30)
theorem v4609_mg_checked : Scalar.distance (sourceCoefficient 80 90 3 2) v4609_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4609_upper : Scalar.QComplex := ((999991605785765216872531117749 : Int)/10^30,(-4097359882501613440875027965 : Int)/10^30)
theorem v4609_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 80 90 5) 1) 14) v4609_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4609 : Material (80 : Basis) (90 : Basis) where
  plus := ![v4609_pa,v4609_pb,v4609_pg]
  minus := ![(Primitive.Addresses.material4609 1).one,v4609_mb,v4609_mg]
  upper := v4609_upper
  lower := (Primitive.Addresses.material4609 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4609_pa_checked.trans (by decide +kernel)
    · exact v4609_pb_checked.trans (by decide +kernel)
    · exact v4609_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 80 90 Primitive.Addresses.material4609
    · exact v4609_mb_checked.trans (by decide +kernel)
    · exact v4609_mg_checked.trans (by decide +kernel)
  upper_error := v4609_upper_checked
  lower_error := reuse_lower_error 80 90 Primitive.Addresses.material4609

def v4610_pa : Scalar.QComplex := ((999997152972964526163767336572 : Int)/10^30,(-2386220016131105155051493084 : Int)/10^30)
theorem v4610_pa_checked : Scalar.distance (sourceCoefficient 80 91 1 0) v4610_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4610_pb : Scalar.QComplex := ((-1029600286542714796950656 : Int)/10^30,(-431476288138844659064975327 : Int)/10^30)
theorem v4610_pb_checked : Scalar.distance (sourceCoefficient 80 91 1 1) v4610_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4610_pg : Scalar.QComplex := ((-93086164399139423678954 : Int)/10^30,(222124701109126486202 : Int)/10^30)
theorem v4610_pg_checked : Scalar.distance (sourceCoefficient 80 91 1 2) v4610_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4610_mb : Scalar.QComplex := ((-1401944506868664005539409 : Int)/10^30,(-431475238981827333597965057 : Int)/10^30)
theorem v4610_mb_checked : Scalar.distance (sourceCoefficient 80 91 3 1) v4610_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4610_mg : Scalar.QComplex := ((-93085938055293237993412 : Int)/10^30,(302453785833192330154 : Int)/10^30)
theorem v4610_mg_checked : Scalar.distance (sourceCoefficient 80 91 3 2) v4610_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4610_upper : Scalar.QComplex := ((999991545195401436749168498032 : Int)/10^30,(-4112120829134973482280020935 : Int)/10^30)
theorem v4610_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 80 91 5) 1) 14) v4610_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4610 : Material (80 : Basis) (91 : Basis) where
  plus := ![v4610_pa,v4610_pb,v4610_pg]
  minus := ![(Primitive.Addresses.material4610 1).one,v4610_mb,v4610_mg]
  upper := v4610_upper
  lower := (Primitive.Addresses.material4610 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4610_pa_checked.trans (by decide +kernel)
    · exact v4610_pb_checked.trans (by decide +kernel)
    · exact v4610_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 80 91 Primitive.Addresses.material4610
    · exact v4610_mb_checked.trans (by decide +kernel)
    · exact v4610_mg_checked.trans (by decide +kernel)
  upper_error := v4610_upper_checked
  lower_error := reuse_lower_error 80 91 Primitive.Addresses.material4610

def v4611_pa : Scalar.QComplex := ((999997076208073154335327626630 : Int)/10^30,(-2418176028566179021054628892 : Int)/10^30)
theorem v4611_pa_checked : Scalar.distance (sourceCoefficient 80 92 1 0) v4611_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4611_pb : Scalar.QComplex := ((-1043388584490338096195071 : Int)/10^30,(-431476253801869794002024489 : Int)/10^30)
theorem v4611_pb_checked : Scalar.distance (sourceCoefficient 80 92 1 1) v4611_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4611_pg : Scalar.QComplex := ((-93086157122346214224535 : Int)/10^30,(225099371888328772793 : Int)/10^30)
theorem v4611_pg_checked : Scalar.distance (sourceCoefficient 80 92 1 2) v4611_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4611_mb : Scalar.QComplex := ((-1415732770051010993927670 : Int)/10^30,(-431475192746185126848013820 : Int)/10^30)
theorem v4611_mb_checked : Scalar.distance (sourceCoefficient 80 92 3 1) v4611_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4611_mg : Scalar.QComplex := ((-93085928211495829768637 : Int)/10^30,(305428449225243931318 : Int)/10^30)
theorem v4611_mg_checked : Scalar.distance (sourceCoefficient 80 92 3 2) v4611_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4611_upper : Scalar.QComplex := ((999991413277445961073652120405 : Int)/10^30,(-4144076661486082191921654057 : Int)/10^30)
theorem v4611_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 80 92 5) 1) 14) v4611_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4611 : Material (80 : Basis) (92 : Basis) where
  plus := ![v4611_pa,v4611_pb,v4611_pg]
  minus := ![(Primitive.Addresses.material4611 1).one,v4611_mb,v4611_mg]
  upper := v4611_upper
  lower := (Primitive.Addresses.material4611 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4611_pa_checked.trans (by decide +kernel)
    · exact v4611_pb_checked.trans (by decide +kernel)
    · exact v4611_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 80 92 Primitive.Addresses.material4611
    · exact v4611_mb_checked.trans (by decide +kernel)
    · exact v4611_mg_checked.trans (by decide +kernel)
  upper_error := v4611_upper_checked
  lower_error := reuse_lower_error 80 92 Primitive.Addresses.material4611

def v4612_pa : Scalar.QComplex := ((999996983778094186083228496601 : Int)/10^30,(-2456101527631390166036879884 : Int)/10^30)
theorem v4612_pa_checked : Scalar.distance (sourceCoefficient 80 93 1 0) v4612_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4612_pb : Scalar.QComplex := ((-1059752580586775842140400 : Int)/10^30,(-431476212288270645320639414 : Int)/10^30)
theorem v4612_pb_checked : Scalar.distance (sourceCoefficient 80 93 1 1) v4612_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4612_pg : Scalar.QComplex := ((-93086148342311415987634 : Int)/10^30,(228629720742845290863 : Int)/10^30)
theorem v4612_pg_checked : Scalar.distance (sourceCoefficient 80 93 1 2) v4612_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4612_mb : Scalar.QComplex := ((-1432096724230018759388994 : Int)/10^30,(-431475137111209811376279017 : Int)/10^30)
theorem v4612_mb_checked : Scalar.distance (sourceCoefficient 80 93 3 1) v4612_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4612_mg : Scalar.QComplex := ((-93085916384932240302215 : Int)/10^30,(308958789188475633148 : Int)/10^30)
theorem v4612_mg_checked : Scalar.distance (sourceCoefficient 80 93 3 2) v4612_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4612_upper : Scalar.QComplex := ((999991255391633844262105607461 : Int)/10^30,(-4182001944539959004329169041 : Int)/10^30)
theorem v4612_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 80 93 5) 1) 14) v4612_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4612 : Material (80 : Basis) (93 : Basis) where
  plus := ![v4612_pa,v4612_pb,v4612_pg]
  minus := ![(Primitive.Addresses.material4612 1).one,v4612_mb,v4612_mg]
  upper := v4612_upper
  lower := (Primitive.Addresses.material4612 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4612_pa_checked.trans (by decide +kernel)
    · exact v4612_pb_checked.trans (by decide +kernel)
    · exact v4612_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 80 93 Primitive.Addresses.material4612
    · exact v4612_mb_checked.trans (by decide +kernel)
    · exact v4612_mg_checked.trans (by decide +kernel)
  upper_error := v4612_upper_checked
  lower_error := reuse_lower_error 80 93 Primitive.Addresses.material4612

def v4613_pa : Scalar.QComplex := ((999996872744836369158283320986 : Int)/10^30,(-2500899947526254993022814269 : Int)/10^30)
theorem v4613_pa_checked : Scalar.distance (sourceCoefficient 80 94 1 0) v4613_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4613_pb : Scalar.QComplex := ((-1079082085933554248907861 : Int)/10^30,(-431476162185492879671858511 : Int)/10^30)
theorem v4613_pb_checked : Scalar.distance (sourceCoefficient 80 94 1 1) v4613_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4613_pg : Scalar.QComplex := ((-93086137769910794330266 : Int)/10^30,(232799845088709294644 : Int)/10^30)
theorem v4613_pg_checked : Scalar.distance (sourceCoefficient 80 94 1 2) v4613_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4613_mb : Scalar.QComplex := ((-1451426179143098257104327 : Int)/10^30,(-431475070327958155615498539 : Int)/10^30)
theorem v4613_mb_checked : Scalar.distance (sourceCoefficient 80 94 3 1) v4613_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4613_mg : Scalar.QComplex := ((-93085902213906060180647 : Int)/10^30,(313128902858106185624 : Int)/10^30)
theorem v4613_mg_checked : Scalar.distance (sourceCoefficient 80 94 3 2) v4613_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4613_upper : Scalar.QComplex := ((999991067040532740701109003998 : Int)/10^30,(-4226800106079509656429518800 : Int)/10^30)
theorem v4613_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 80 94 5) 1) 14) v4613_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4613 : Material (80 : Basis) (94 : Basis) where
  plus := ![v4613_pa,v4613_pb,v4613_pg]
  minus := ![(Primitive.Addresses.material4613 1).one,v4613_mb,v4613_mg]
  upper := v4613_upper
  lower := (Primitive.Addresses.material4613 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4613_pa_checked.trans (by decide +kernel)
    · exact v4613_pb_checked.trans (by decide +kernel)
    · exact v4613_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 80 94 Primitive.Addresses.material4613
    · exact v4613_mb_checked.trans (by decide +kernel)
    · exact v4613_mg_checked.trans (by decide +kernel)
  upper_error := v4613_upper_checked
  lower_error := reuse_lower_error 80 94 Primitive.Addresses.material4613

def v4614_pa : Scalar.QComplex := ((999996761039332366518407960662 : Int)/10^30,(-2545174030277842652526332275 : Int)/10^30)
theorem v4614_pa_checked : Scalar.distance (sourceCoefficient 80 95 1 0) v4614_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4614_pb : Scalar.QComplex := ((-1098185350742652380097478 : Int)/10^30,(-431476111534743691391670479 : Int)/10^30)
theorem v4614_pb_checked : Scalar.distance (sourceCoefficient 80 95 1 1) v4614_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4614_pg : Scalar.QComplex := ((-93086127107112333313730 : Int)/10^30,(236921160670485377286 : Int)/10^30)
theorem v4614_pg_checked : Scalar.distance (sourceCoefficient 80 95 1 2) v4614_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4614_mb : Scalar.QComplex := ((-1470529393129862513109362 : Int)/10^30,(-431475003191970675780627668 : Int)/10^30)
theorem v4614_mb_checked : Scalar.distance (sourceCoefficient 80 95 3 1) v4614_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4614_mg : Scalar.QComplex := ((-93085887994601839501904 : Int)/10^30,(317250207703813286502 : Int)/10^30)
theorem v4614_mg_checked : Scalar.distance (sourceCoefficient 80 95 3 2) v4614_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4614_upper : Scalar.QComplex := ((999990878922144794459238096153 : Int)/10^30,(-4271073930096485792144878258 : Int)/10^30)
theorem v4614_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 80 95 5) 1) 14) v4614_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4614 : Material (80 : Basis) (95 : Basis) where
  plus := ![v4614_pa,v4614_pb,v4614_pg]
  minus := ![(Primitive.Addresses.material4614 1).one,v4614_mb,v4614_mg]
  upper := v4614_upper
  lower := (Primitive.Addresses.material4614 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4614_pa_checked.trans (by decide +kernel)
    · exact v4614_pb_checked.trans (by decide +kernel)
    · exact v4614_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 80 95 Primitive.Addresses.material4614
    · exact v4614_mb_checked.trans (by decide +kernel)
    · exact v4614_mg_checked.trans (by decide +kernel)
  upper_error := v4614_upper_checked
  lower_error := reuse_lower_error 80 95 Primitive.Addresses.material4614

def v4615_pa : Scalar.QComplex := ((999996706692425631575686174263 : Int)/10^30,(-2566438057476172409328890145 : Int)/10^30)
theorem v4615_pa_checked : Scalar.distance (sourceCoefficient 80 96 1 0) v4615_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4615_pb : Scalar.QComplex := ((-1107360296951060367982662 : Int)/10^30,(-431476086807245259130437037 : Int)/10^30)
theorem v4615_pb_checked : Scalar.distance (sourceCoefficient 80 96 1 1) v4615_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4615_pg : Scalar.QComplex := ((-93086121910292516672668 : Int)/10^30,(238900552666440914929 : Int)/10^30)
theorem v4615_pg_checked : Scalar.distance (sourceCoefficient 80 96 1 2) v4615_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4615_mb : Scalar.QComplex := ((-1479704314583301249993917 : Int)/10^30,(-431474970546916097078691470 : Int)/10^30)
theorem v4615_mb_checked : Scalar.distance (sourceCoefficient 80 96 3 1) v4615_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4615_mg : Scalar.QComplex := ((-93085881089657813870886 : Int)/10^30,(319229594478129275682 : Int)/10^30)
theorem v4615_mg_checked : Scalar.distance (sourceCoefficient 80 96 3 2) v4615_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4615_upper : Scalar.QComplex := ((999990787875537116011364061181 : Int)/10^30,(-4292337831826714173488603709 : Int)/10^30)
theorem v4615_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 80 96 5) 1) 14) v4615_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4615 : Material (80 : Basis) (96 : Basis) where
  plus := ![v4615_pa,v4615_pb,v4615_pg]
  minus := ![(Primitive.Addresses.material4615 1).one,v4615_mb,v4615_mg]
  upper := v4615_upper
  lower := (Primitive.Addresses.material4615 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4615_pa_checked.trans (by decide +kernel)
    · exact v4615_pb_checked.trans (by decide +kernel)
    · exact v4615_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 80 96 Primitive.Addresses.material4615
    · exact v4615_mb_checked.trans (by decide +kernel)
    · exact v4615_mg_checked.trans (by decide +kernel)
  upper_error := v4615_upper_checked
  lower_error := reuse_lower_error 80 96 Primitive.Addresses.material4615

def v4616_pa : Scalar.QComplex := ((999996516249764901668047116002 : Int)/10^30,(-2639600032899106356215647156 : Int)/10^30)
theorem v4616_pa_checked : Scalar.distance (sourceCoefficient 80 97 1 0) v4616_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4616_pb : Scalar.QComplex := ((-1138928030853546402471026 : Int)/10^30,(-431475999741467021783406588 : Int)/10^30)
theorem v4616_pb_checked : Scalar.distance (sourceCoefficient 80 97 1 1) v4616_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4616_pg : Scalar.QComplex := ((-93086103654746847460473 : Int)/10^30,(245710938265058350109 : Int)/10^30)
theorem v4616_pg_checked : Scalar.distance (sourceCoefficient 80 97 1 2) v4616_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4616_mb : Scalar.QComplex := ((-1511271961597831914131668 : Int)/10^30,(-431474856239637678411385414 : Int)/10^30)
theorem v4616_mb_checked : Scalar.distance (sourceCoefficient 80 97 3 1) v4616_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4616_mg : Scalar.QComplex := ((-93085856957062898806886 : Int)/10^30,(326039961787215189224 : Int)/10^30)
theorem v4616_mg_checked : Scalar.distance (sourceCoefficient 80 97 3 2) v4616_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4616_upper : Scalar.QComplex := ((999990471162227650655310891185 : Int)/10^30,(-4365499369596724340660399310 : Int)/10^30)
theorem v4616_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 80 97 5) 1) 14) v4616_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4616 : Material (80 : Basis) (97 : Basis) where
  plus := ![v4616_pa,v4616_pb,v4616_pg]
  minus := ![(Primitive.Addresses.material4616 1).one,v4616_mb,v4616_mg]
  upper := v4616_upper
  lower := (Primitive.Addresses.material4616 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4616_pa_checked.trans (by decide +kernel)
    · exact v4616_pb_checked.trans (by decide +kernel)
    · exact v4616_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 80 97 Primitive.Addresses.material4616
    · exact v4616_mb_checked.trans (by decide +kernel)
    · exact v4616_mg_checked.trans (by decide +kernel)
  upper_error := v4616_upper_checked
  lower_error := reuse_lower_error 80 97 Primitive.Addresses.material4616

def v4617_pa : Scalar.QComplex := ((999997579282769957025751007871 : Int)/10^30,(-2200324657911654788864921907 : Int)/10^30)
theorem v4617_pa_checked : Scalar.distance (sourceCoefficient 81 82 1 0) v4617_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4617_pb : Scalar.QComplex := ((-949390628776695257741285 : Int)/10^30,(-431476476508477603525935657 : Int)/10^30)
theorem v4617_pb_checked : Scalar.distance (sourceCoefficient 81 82 1 1) v4617_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4617_pg : Scalar.QComplex := ((-93086204560284837938377 : Int)/10^30,(204820367017594559241 : Int)/10^30)
theorem v4617_pg_checked : Scalar.distance (sourceCoefficient 81 82 1 2) v4617_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4617_mb : Scalar.QComplex := ((-1321735041522875192808789 : Int)/10^30,(-431475496568712282627376758 : Int)/10^30)
theorem v4617_mb_checked : Scalar.distance (sourceCoefficient 81 82 3 1) v4617_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4617_mg : Scalar.QComplex := ((-93085993149284661138652 : Int)/10^30,(285149492842114534268 : Int)/10^30)
theorem v4617_mg_checked : Scalar.distance (sourceCoefficient 81 82 3 2) v4617_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4617_upper : Scalar.QComplex := ((999992292343095920844138228264 : Int)/10^30,(-3926226483556872031464479788 : Int)/10^30)
theorem v4617_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 81 82 5) 1) 14) v4617_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4617 : Material (81 : Basis) (82 : Basis) where
  plus := ![v4617_pa,v4617_pb,v4617_pg]
  minus := ![(Primitive.Addresses.material4617 1).one,v4617_mb,v4617_mg]
  upper := v4617_upper
  lower := (Primitive.Addresses.material4617 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4617_pa_checked.trans (by decide +kernel)
    · exact v4617_pb_checked.trans (by decide +kernel)
    · exact v4617_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 81 82 Primitive.Addresses.material4617
    · exact v4617_mb_checked.trans (by decide +kernel)
    · exact v4617_mg_checked.trans (by decide +kernel)
  upper_error := v4617_upper_checked
  lower_error := reuse_lower_error 81 82 Primitive.Addresses.material4617

def v4618_pa : Scalar.QComplex := ((999997549335345483976105918107 : Int)/10^30,(-2213893245681642819809136104 : Int)/10^30)
theorem v4618_pa_checked : Scalar.distance (sourceCoefficient 81 83 1 0) v4618_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4618_pb : Scalar.QComplex := ((-955245169318815334793467 : Int)/10^30,(-431476463554198908403001277 : Int)/10^30)
theorem v4618_pb_checked : Scalar.distance (sourceCoefficient 81 83 1 1) v4618_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4618_pg : Scalar.QComplex := ((-93086201769065344099452 : Int)/10^30,(206083418404041720947 : Int)/10^30)
theorem v4618_pg_checked : Scalar.distance (sourceCoefficient 81 83 1 2) v4618_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4618_mb : Scalar.QComplex := ((-1327589568706123185471936 : Int)/10^30,(-431475478562233601842616845 : Int)/10^30)
theorem v4618_mb_checked : Scalar.distance (sourceCoefficient 81 83 3 1) v4618_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4618_mg : Scalar.QComplex := ((-93085989268109745817157 : Int)/10^30,(286412541349573229176 : Int)/10^30)
theorem v4618_mg_checked : Scalar.distance (sourceCoefficient 81 83 3 2) v4618_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4618_upper : Scalar.QComplex := ((999992238977564492633007744561 : Int)/10^30,(-3939794999431504625936786824 : Int)/10^30)
theorem v4618_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 81 83 5) 1) 14) v4618_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4618 : Material (81 : Basis) (83 : Basis) where
  plus := ![v4618_pa,v4618_pb,v4618_pg]
  minus := ![(Primitive.Addresses.material4618 1).one,v4618_mb,v4618_mg]
  upper := v4618_upper
  lower := (Primitive.Addresses.material4618 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4618_pa_checked.trans (by decide +kernel)
    · exact v4618_pb_checked.trans (by decide +kernel)
    · exact v4618_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 81 83 Primitive.Addresses.material4618
    · exact v4618_mb_checked.trans (by decide +kernel)
    · exact v4618_mg_checked.trans (by decide +kernel)
  upper_error := v4618_upper_checked
  lower_error := reuse_lower_error 81 83 Primitive.Addresses.material4618

def v4619_pa : Scalar.QComplex := ((999997470923848978254622634993 : Int)/10^30,(-2249032215380053885226215085 : Int)/10^30)
theorem v4619_pa_checked : Scalar.distance (sourceCoefficient 81 84 1 0) v4619_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4619_pb : Scalar.QComplex := ((-970406844386492858237568 : Int)/10^30,(-431476429513794954096794630 : Int)/10^30)
theorem v4619_pb_checked : Scalar.distance (sourceCoefficient 81 84 1 1) v4619_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4619_pg : Scalar.QComplex := ((-93086194447624759088953 : Int)/10^30,(209354379593008523915 : Int)/10^30)
theorem v4619_pg_checked : Scalar.distance (sourceCoefficient 81 84 1 2) v4619_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4619_mb : Scalar.QComplex := ((-1342751208753080668753671 : Int)/10^30,(-431475431437999595425046493 : Int)/10^30)
theorem v4619_mb_checked : Scalar.distance (sourceCoefficient 81 84 3 1) v4619_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4619_mg : Scalar.QComplex := ((-93085979123979699458469 : Int)/10^30,(289683495002538211760 : Int)/10^30)
theorem v4619_mg_checked : Scalar.distance (sourceCoefficient 81 84 3 2) v4619_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4619_upper : Scalar.QComplex := ((999992099919510854596659488609 : Int)/10^30,(-3974933781463418505428017535 : Int)/10^30)
theorem v4619_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 81 84 5) 1) 14) v4619_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4619 : Material (81 : Basis) (84 : Basis) where
  plus := ![v4619_pa,v4619_pb,v4619_pg]
  minus := ![(Primitive.Addresses.material4619 1).one,v4619_mb,v4619_mg]
  upper := v4619_upper
  lower := (Primitive.Addresses.material4619 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4619_pa_checked.trans (by decide +kernel)
    · exact v4619_pb_checked.trans (by decide +kernel)
    · exact v4619_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 81 84 Primitive.Addresses.material4619
    · exact v4619_mb_checked.trans (by decide +kernel)
    · exact v4619_mg_checked.trans (by decide +kernel)
  upper_error := v4619_upper_checked
  lower_error := reuse_lower_error 81 84 Primitive.Addresses.material4619

def v4620_pa : Scalar.QComplex := ((999997289997537595262027138210 : Int)/10^30,(-2328088825774508481303428342 : Int)/10^30)
theorem v4620_pa_checked : Scalar.distance (sourceCoefficient 81 85 1 0) v4620_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4620_pb : Scalar.QComplex := ((-1004517992039793221368715 : Int)/10^30,(-431476350331856075488114305 : Int)/10^30)
theorem v4620_pb_checked : Scalar.distance (sourceCoefficient 81 85 1 1) v4620_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4620_pg : Scalar.QComplex := ((-93086177485425488247483 : Int)/10^30,(216713476931937835358 : Int)/10^30)
theorem v4620_pg_checked : Scalar.distance (sourceCoefficient 81 85 1 2) v4620_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4620_mb : Scalar.QComplex := ((-1376862275374794774002738 : Int)/10^30,(-431475322819706084132622276 : Int)/10^30)
theorem v4620_mb_checked : Scalar.distance (sourceCoefficient 81 85 3 1) v4620_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4620_mg : Scalar.QComplex := ((-93085955811217182363464 : Int)/10^30,(297042574963725234916 : Int)/10^30)
theorem v4620_mg_checked : Scalar.distance (sourceCoefficient 81 85 3 2) v4620_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4620_upper : Scalar.QComplex := ((999991782548931358933849141725 : Int)/10^30,(-4053989961849938620481216139 : Int)/10^30)
theorem v4620_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 81 85 5) 1) 14) v4620_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4620 : Material (81 : Basis) (85 : Basis) where
  plus := ![v4620_pa,v4620_pb,v4620_pg]
  minus := ![(Primitive.Addresses.material4620 1).one,v4620_mb,v4620_mg]
  upper := v4620_upper
  lower := (Primitive.Addresses.material4620 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4620_pa_checked.trans (by decide +kernel)
    · exact v4620_pb_checked.trans (by decide +kernel)
    · exact v4620_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 81 85 Primitive.Addresses.material4620
    · exact v4620_mb_checked.trans (by decide +kernel)
    · exact v4620_mg_checked.trans (by decide +kernel)
  upper_error := v4620_upper_checked
  lower_error := reuse_lower_error 81 85 Primitive.Addresses.material4620

def v4621_pa : Scalar.QComplex := ((999997255936835004412460416946 : Int)/10^30,(-2342673430102565873544419735 : Int)/10^30)
theorem v4621_pa_checked : Scalar.distance (sourceCoefficient 81 86 1 0) v4621_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4621_pb : Scalar.QComplex := ((-1010810920227619442563017 : Int)/10^30,(-431476335331276508058681989 : Int)/10^30)
theorem v4621_pb_checked : Scalar.distance (sourceCoefficient 81 86 1 1) v4621_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4621_pg : Scalar.QComplex := ((-93086174282027589903799 : Int)/10^30,(218071105601291056540 : Int)/10^30)
theorem v4621_pg_checked : Scalar.distance (sourceCoefficient 81 86 1 2) v4621_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4621_mb : Scalar.QComplex := ((-1383155188274651664176004 : Int)/10^30,(-431475302388618498974919080 : Int)/10^30)
theorem v4621_mb_checked : Scalar.distance (sourceCoefficient 81 86 3 1) v4621_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4621_mg : Scalar.QComplex := ((-93085951436248080464837 : Int)/10^30,(298400200363183145218 : Int)/10^30)
theorem v4621_mg_checked : Scalar.distance (sourceCoefficient 81 86 3 2) v4621_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4621_upper : Scalar.QComplex := ((999991723316575532241793843212 : Int)/10^30,(-4068574485670258385048021437 : Int)/10^30)
theorem v4621_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 81 86 5) 1) 14) v4621_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4621 : Material (81 : Basis) (86 : Basis) where
  plus := ![v4621_pa,v4621_pb,v4621_pg]
  minus := ![(Primitive.Addresses.material4621 1).one,v4621_mb,v4621_mg]
  upper := v4621_upper
  lower := (Primitive.Addresses.material4621 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4621_pa_checked.trans (by decide +kernel)
    · exact v4621_pb_checked.trans (by decide +kernel)
    · exact v4621_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 81 86 Primitive.Addresses.material4621
    · exact v4621_mb_checked.trans (by decide +kernel)
    · exact v4621_mg_checked.trans (by decide +kernel)
  upper_error := v4621_upper_checked
  lower_error := reuse_lower_error 81 86 Primitive.Addresses.material4621

def v4622_pa : Scalar.QComplex := ((999997253673916710029051256408 : Int)/10^30,(-2343639183891792277407798007 : Int)/10^30)
theorem v4622_pa_checked : Scalar.distance (sourceCoefficient 81 87 1 0) v4622_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4622_pb : Scalar.QComplex := ((-1011227621227148697245591 : Int)/10^30,(-431476334333658013010376259 : Int)/10^30)
theorem v4622_pb_checked : Scalar.distance (sourceCoefficient 81 87 1 1) v4622_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4622_pg : Scalar.QComplex := ((-93086174069091603541381 : Int)/10^30,(218161004168151266170 : Int)/10^30)
theorem v4622_pg_checked : Scalar.distance (sourceCoefficient 81 87 1 2) v4622_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4622_mb : Scalar.QComplex := ((-1383571888258124262399766 : Int)/10^30,(-431475301031406180308161527 : Int)/10^30)
theorem v4622_mb_checked : Scalar.distance (sourceCoefficient 81 87 3 1) v4622_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4622_mg : Scalar.QComplex := ((-93085951145733759069006 : Int)/10^30,(298490098712815843888 : Int)/10^30)
theorem v4622_mg_checked : Scalar.distance (sourceCoefficient 81 87 3 2) v4622_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4622_upper : Scalar.QComplex := ((999991719386857180503957375396 : Int)/10^30,(-4069540234115516279506121126 : Int)/10^30)
theorem v4622_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 81 87 5) 1) 14) v4622_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4622 : Material (81 : Basis) (87 : Basis) where
  plus := ![v4622_pa,v4622_pb,v4622_pg]
  minus := ![(Primitive.Addresses.material4622 1).one,v4622_mb,v4622_mg]
  upper := v4622_upper
  lower := (Primitive.Addresses.material4622 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4622_pa_checked.trans (by decide +kernel)
    · exact v4622_pb_checked.trans (by decide +kernel)
    · exact v4622_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 81 87 Primitive.Addresses.material4622
    · exact v4622_mb_checked.trans (by decide +kernel)
    · exact v4622_mg_checked.trans (by decide +kernel)
  upper_error := v4622_upper_checked
  lower_error := reuse_lower_error 81 87 Primitive.Addresses.material4622

def v4623_pa : Scalar.QComplex := ((999997226044528637084977997286 : Int)/10^30,(-2355398744989237048428768254 : Int)/10^30)
theorem v4623_pa_checked : Scalar.distance (sourceCoefficient 81 88 1 0) v4623_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4623_pb : Scalar.QComplex := ((-1016301606843711444027772 : Int)/10^30,(-431476322143048668284659695 : Int)/10^30)
theorem v4623_pb_checked : Scalar.distance (sourceCoefficient 81 88 1 1) v4623_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4623_pg : Scalar.QComplex := ((-93086171468137519721432 : Int)/10^30,(219255659657340773249 : Int)/10^30)
theorem v4623_pg_checked : Scalar.distance (sourceCoefficient 81 88 1 2) v4623_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4623_mb : Scalar.QComplex := ((-1388645861465463451702330 : Int)/10^30,(-431475284462180311438758600 : Int)/10^30)
theorem v4623_mb_checked : Scalar.distance (sourceCoefficient 81 88 3 1) v4623_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4623_mg : Scalar.QComplex := ((-93085947600142257985666 : Int)/10^30,(299584751549908852402 : Int)/10^30)
theorem v4623_mg_checked : Scalar.distance (sourceCoefficient 81 88 3 2) v4623_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4623_upper : Scalar.QComplex := ((999991671461574623147395179909 : Int)/10^30,(-4081299730012658875570576845 : Int)/10^30)
theorem v4623_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 81 88 5) 1) 14) v4623_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4623 : Material (81 : Basis) (88 : Basis) where
  plus := ![v4623_pa,v4623_pb,v4623_pg]
  minus := ![(Primitive.Addresses.material4623 1).one,v4623_mb,v4623_mg]
  upper := v4623_upper
  lower := (Primitive.Addresses.material4623 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4623_pa_checked.trans (by decide +kernel)
    · exact v4623_pb_checked.trans (by decide +kernel)
    · exact v4623_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 81 88 Primitive.Addresses.material4623
    · exact v4623_mb_checked.trans (by decide +kernel)
    · exact v4623_mg_checked.trans (by decide +kernel)
  upper_error := v4623_upper_checked
  lower_error := reuse_lower_error 81 88 Primitive.Addresses.material4623

def v4624_pa : Scalar.QComplex := ((999997188017941578250420594126 : Int)/10^30,(-2371488184579548410825227056 : Int)/10^30)
theorem v4624_pa_checked : Scalar.distance (sourceCoefficient 81 89 1 0) v4624_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4624_pb : Scalar.QComplex := ((-1023243837371203051905359 : Int)/10^30,(-431476305334958213898576185 : Int)/10^30)
theorem v4624_pb_checked : Scalar.distance (sourceCoefficient 81 89 1 1) v4624_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4624_pg : Scalar.QComplex := ((-93086167885179519953798 : Int)/10^30,(220753368042001711239 : Int)/10^30)
theorem v4624_pg_checked : Scalar.distance (sourceCoefficient 81 89 1 2) v4624_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4624_mb : Scalar.QComplex := ((-1395588074903420304743359 : Int)/10^30,(-431475261663263836703895128 : Int)/10^30)
theorem v4624_mb_checked : Scalar.distance (sourceCoefficient 81 89 3 1) v4624_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4624_mg : Scalar.QComplex := ((-93085942724730710636279 : Int)/10^30,(301082456284973126766 : Int)/10^30)
theorem v4624_mg_checked : Scalar.distance (sourceCoefficient 81 89 3 2) v4624_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4624_upper : Scalar.QComplex := ((999991605666131090127621061399 : Int)/10^30,(-4097389080009200448019283544 : Int)/10^30)
theorem v4624_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 81 89 5) 1) 14) v4624_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4624 : Material (81 : Basis) (89 : Basis) where
  plus := ![v4624_pa,v4624_pb,v4624_pg]
  minus := ![(Primitive.Addresses.material4624 1).one,v4624_mb,v4624_mg]
  upper := v4624_upper
  lower := (Primitive.Addresses.material4624 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4624_pa_checked.trans (by decide +kernel)
    · exact v4624_pb_checked.trans (by decide +kernel)
    · exact v4624_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 81 89 Primitive.Addresses.material4624
    · exact v4624_mb_checked.trans (by decide +kernel)
    · exact v4624_mg_checked.trans (by decide +kernel)
  upper_error := v4624_upper_checked
  lower_error := reuse_lower_error 81 89 Primitive.Addresses.material4624

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
