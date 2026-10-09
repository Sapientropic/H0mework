import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B065
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B066

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1569_pa : Scalar.QComplex := ((999999425402672221465106380895 : Int)/10^30,(-1072004815938333691684338345 : Int)/10^30)
theorem v1569_pa_checked : Scalar.distance (sourceCoefficient 17 74 1 0) v1569_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1569_pb : Scalar.QComplex := ((-462545912002348949768668 : Int)/10^30,(-431477209195029908286357204 : Int)/10^30)
theorem v1569_pb_checked : Scalar.distance (sourceCoefficient 17 74 1 1) v1569_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1569_pg : Scalar.QComplex := ((-93086369519088225094379 : Int)/10^30,(99789093761224505109 : Int)/10^30)
theorem v1569_pg_checked : Scalar.distance (sourceCoefficient 17 74 1 2) v1569_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1569_mb : Scalar.QComplex := ((-834891138298562504321442 : Int)/10^30,(-431476649380055678872621038 : Int)/10^30)
theorem v1569_mb_checked : Scalar.distance (sourceCoefficient 17 74 3 1) v1569_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1569_mg : Scalar.QComplex := ((-93086248745285013894977 : Int)/10^30,(180118401045705534210 : Int)/10^30)
theorem v1569_mg_checked : Scalar.distance (sourceCoefficient 17 74 3 2) v1569_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1569_upper : Scalar.QComplex := ((999996085837935476033322563619 : Int)/10^30,(-2797911508318886413517334526 : Int)/10^30)
theorem v1569_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 74 5) 1) 14) v1569_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1569 : Material (17 : Basis) (74 : Basis) where
  plus := ![v1569_pa,v1569_pb,v1569_pg]
  minus := ![(Primitive.Addresses.material1569 1).one,v1569_mb,v1569_mg]
  upper := v1569_upper
  lower := (Primitive.Addresses.material1569 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1569_pa_checked.trans (by decide +kernel)
    · exact v1569_pb_checked.trans (by decide +kernel)
    · exact v1569_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 74 Primitive.Addresses.material1569
    · exact v1569_mb_checked.trans (by decide +kernel)
    · exact v1569_mg_checked.trans (by decide +kernel)
  upper_error := v1569_upper_checked
  lower_error := reuse_lower_error 17 74 Primitive.Addresses.material1569

def v1570_pa : Scalar.QComplex := ((999999409411038688534434547502 : Int)/10^30,(-1086819936248691523766535544 : Int)/10^30)
theorem v1570_pa_checked : Scalar.distance (sourceCoefficient 17 75 1 0) v1570_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1570_pb : Scalar.QComplex := ((-468938300241025794355082 : Int)/10^30,(-431477200270954004139259652 : Int)/10^30)
theorem v1570_pb_checked : Scalar.distance (sourceCoefficient 17 75 1 1) v1570_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1570_pg : Scalar.QComplex := ((-93086367812151601769042 : Int)/10^30,(101168180080035245749 : Int)/10^30)
theorem v1570_pg_checked : Scalar.distance (sourceCoefficient 17 75 1 2) v1570_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1570_mb : Scalar.QComplex := ((-841283516455985481253229 : Int)/10^30,(-431476634939639950067543763 : Int)/10^30)
theorem v1570_mb_checked : Scalar.distance (sourceCoefficient 17 75 3 1) v1570_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1570_mg : Scalar.QComplex := ((-93086245848259644748590 : Int)/10^30,(181497485378009982641 : Int)/10^30)
theorem v1570_mg_checked : Scalar.distance (sourceCoefficient 17 75 3 2) v1570_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1570_upper : Scalar.QComplex := ((999996044276772122300339959444 : Int)/10^30,(-2812726578963754121426177505 : Int)/10^30)
theorem v1570_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 75 5) 1) 14) v1570_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1570 : Material (17 : Basis) (75 : Basis) where
  plus := ![v1570_pa,v1570_pb,v1570_pg]
  minus := ![(Primitive.Addresses.material1570 1).one,v1570_mb,v1570_mg]
  upper := v1570_upper
  lower := (Primitive.Addresses.material1570 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1570_pa_checked.trans (by decide +kernel)
    · exact v1570_pb_checked.trans (by decide +kernel)
    · exact v1570_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 75 Primitive.Addresses.material1570
    · exact v1570_mb_checked.trans (by decide +kernel)
    · exact v1570_mg_checked.trans (by decide +kernel)
  upper_error := v1570_upper_checked
  lower_error := reuse_lower_error 17 75 Primitive.Addresses.material1570

def v1571_pa : Scalar.QComplex := ((999999395824411150572200488911 : Int)/10^30,(-1099250113791539908553467742 : Int)/10^30)
theorem v1571_pa_checked : Scalar.distance (sourceCoefficient 17 76 1 0) v1571_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1571_pb : Scalar.QComplex := ((-474301639720079580835718 : Int)/10^30,(-431477192686061332309229982 : Int)/10^30)
theorem v1571_pb_checked : Scalar.distance (sourceCoefficient 17 76 1 1) v1571_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1571_pg : Scalar.QComplex := ((-93086366361608561968969 : Int)/10^30,(102325260637863784576 : Int)/10^30)
theorem v1571_pg_checked : Scalar.distance (sourceCoefficient 17 76 1 2) v1571_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1571_mb : Scalar.QComplex := ((-846646847392602098054367 : Int)/10^30,(-431476622726429687859446990 : Int)/10^30)
theorem v1571_mb_checked : Scalar.distance (sourceCoefficient 17 76 3 1) v1571_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1571_mg : Scalar.QComplex := ((-93086243399208736619755 : Int)/10^30,(182654564253251235280 : Int)/10^30)
theorem v1571_mg_checked : Scalar.distance (sourceCoefficient 17 76 3 2) v1571_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1571_upper : Scalar.QComplex := ((999996009236806037965429100252 : Int)/10^30,(-2825156714544026646063778285 : Int)/10^30)
theorem v1571_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 76 5) 1) 14) v1571_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1571 : Material (17 : Basis) (76 : Basis) where
  plus := ![v1571_pa,v1571_pb,v1571_pg]
  minus := ![(Primitive.Addresses.material1571 1).one,v1571_mb,v1571_mg]
  upper := v1571_upper
  lower := (Primitive.Addresses.material1571 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1571_pa_checked.trans (by decide +kernel)
    · exact v1571_pb_checked.trans (by decide +kernel)
    · exact v1571_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 76 Primitive.Addresses.material1571
    · exact v1571_mb_checked.trans (by decide +kernel)
    · exact v1571_mg_checked.trans (by decide +kernel)
  upper_error := v1571_upper_checked
  lower_error := reuse_lower_error 17 76 Primitive.Addresses.material1571

def v1572_pa : Scalar.QComplex := ((999999392656965760779336342304 : Int)/10^30,(-1102127805480326355245848391 : Int)/10^30)
theorem v1572_pa_checked : Scalar.distance (sourceCoefficient 17 77 1 0) v1572_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1572_pb : Scalar.QComplex := ((-475543298358544727573279 : Int)/10^30,(-431477190917422797333960563 : Int)/10^30)
theorem v1572_pb_checked : Scalar.distance (sourceCoefficient 17 77 1 1) v1572_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1572_pg : Scalar.QComplex := ((-93086366023403517860725 : Int)/10^30,(102593134614737801712 : Int)/10^30)
theorem v1572_pg_checked : Scalar.distance (sourceCoefficient 17 77 1 2) v1572_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1572_mb : Scalar.QComplex := ((-847888504042485587927205 : Int)/10^30,(-431476619886296328662859026 : Int)/10^30)
theorem v1572_mb_checked : Scalar.distance (sourceCoefficient 17 77 3 1) v1572_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1572_mg : Scalar.QComplex := ((-93086242829840640994488 : Int)/10^30,(182922437838527807504 : Int)/10^30)
theorem v1572_mg_checked : Scalar.distance (sourceCoefficient 17 77 3 2) v1572_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1572_upper : Scalar.QComplex := ((999996001102730573015692885768 : Int)/10^30,(-2828034396480105965338980439 : Int)/10^30)
theorem v1572_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 77 5) 1) 14) v1572_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1572 : Material (17 : Basis) (77 : Basis) where
  plus := ![v1572_pa,v1572_pb,v1572_pg]
  minus := ![(Primitive.Addresses.material1572 1).one,v1572_mb,v1572_mg]
  upper := v1572_upper
  lower := (Primitive.Addresses.material1572 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1572_pa_checked.trans (by decide +kernel)
    · exact v1572_pb_checked.trans (by decide +kernel)
    · exact v1572_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 77 Primitive.Addresses.material1572
    · exact v1572_mb_checked.trans (by decide +kernel)
    · exact v1572_mg_checked.trans (by decide +kernel)
  upper_error := v1572_upper_checked
  lower_error := reuse_lower_error 17 77 Primitive.Addresses.material1572

def v1573_pa : Scalar.QComplex := ((999999373440969619457089949785 : Int)/10^30,(-1119427384060648781078352633 : Int)/10^30)
theorem v1573_pa_checked : Scalar.distance (sourceCoefficient 17 78 1 0) v1573_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1573_pb : Scalar.QComplex := ((-483007673728775411561045 : Int)/10^30,(-431477180184639049938206060 : Int)/10^30)
theorem v1573_pb_checked : Scalar.distance (sourceCoefficient 17 78 1 1) v1573_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1573_pg : Scalar.QComplex := ((-93086363971290487928283 : Int)/10^30,(104203490201736919584 : Int)/10^30)
theorem v1573_pg_checked : Scalar.distance (sourceCoefficient 17 78 1 2) v1573_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1573_mb : Scalar.QComplex := ((-855352867371479195404361 : Int)/10^30,(-431476602712096816050901947 : Int)/10^30)
theorem v1573_mb_checked : Scalar.distance (sourceCoefficient 17 78 3 1) v1573_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1573_mg : Scalar.QComplex := ((-93086239388064031300558 : Int)/10^30,(184532791055036822359 : Int)/10^30)
theorem v1573_mg_checked : Scalar.distance (sourceCoefficient 17 78 3 2) v1573_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1573_upper : Scalar.QComplex := ((999995952029259827535206329390 : Int)/10^30,(-2845333916129672168662247154 : Int)/10^30)
theorem v1573_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 78 5) 1) 14) v1573_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1573 : Material (17 : Basis) (78 : Basis) where
  plus := ![v1573_pa,v1573_pb,v1573_pg]
  minus := ![(Primitive.Addresses.material1573 1).one,v1573_mb,v1573_mg]
  upper := v1573_upper
  lower := (Primitive.Addresses.material1573 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1573_pa_checked.trans (by decide +kernel)
    · exact v1573_pb_checked.trans (by decide +kernel)
    · exact v1573_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 78 Primitive.Addresses.material1573
    · exact v1573_mb_checked.trans (by decide +kernel)
    · exact v1573_mg_checked.trans (by decide +kernel)
  upper_error := v1573_upper_checked
  lower_error := reuse_lower_error 17 78 Primitive.Addresses.material1573

def v1574_pa : Scalar.QComplex := ((999999367182280439820723330551 : Int)/10^30,(-1125004461618749476501116226 : Int)/10^30)
theorem v1574_pa_checked : Scalar.distance (sourceCoefficient 17 79 1 0) v1574_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1574_pb : Scalar.QComplex := ((-485414056039142157756132 : Int)/10^30,(-431477176687879725137656040 : Int)/10^30)
theorem v1574_pb_checked : Scalar.distance (sourceCoefficient 17 79 1 1) v1574_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1574_pg : Scalar.QComplex := ((-93086363302797691316717 : Int)/10^30,(104722640301853657215 : Int)/10^30)
theorem v1574_pg_checked : Scalar.distance (sourceCoefficient 17 79 1 2) v1574_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1574_mb : Scalar.QComplex := ((-857759245768294021236223 : Int)/10^30,(-431476597138739238843181519 : Int)/10^30)
theorem v1574_mb_checked : Scalar.distance (sourceCoefficient 17 79 3 1) v1574_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1574_mg : Scalar.QComplex := ((-93086238271568328851209 : Int)/10^30,(185051940384971075707 : Int)/10^30)
theorem v1574_mg_checked : Scalar.distance (sourceCoefficient 17 79 3 2) v1574_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1574_upper : Scalar.QComplex := ((999995936145050052723193123310 : Int)/10^30,(-2850910974579441230639064128 : Int)/10^30)
theorem v1574_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 79 5) 1) 14) v1574_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1574 : Material (17 : Basis) (79 : Basis) where
  plus := ![v1574_pa,v1574_pb,v1574_pg]
  minus := ![(Primitive.Addresses.material1574 1).one,v1574_mb,v1574_mg]
  upper := v1574_upper
  lower := (Primitive.Addresses.material1574 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1574_pa_checked.trans (by decide +kernel)
    · exact v1574_pb_checked.trans (by decide +kernel)
    · exact v1574_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 79 Primitive.Addresses.material1574
    · exact v1574_mb_checked.trans (by decide +kernel)
    · exact v1574_mg_checked.trans (by decide +kernel)
  upper_error := v1574_upper_checked
  lower_error := reuse_lower_error 17 79 Primitive.Addresses.material1574

def v1575_pa : Scalar.QComplex := ((999999357343346678227456350978 : Int)/10^30,(-1133716407941585287770524463 : Int)/10^30)
theorem v1575_pa_checked : Scalar.distance (sourceCoefficient 17 80 1 0) v1575_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1575_pb : Scalar.QComplex := ((-489173063000406099490983 : Int)/10^30,(-431477171189787659206252263 : Int)/10^30)
theorem v1575_pb_checked : Scalar.distance (sourceCoefficient 17 80 1 1) v1575_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1575_pg : Scalar.QComplex := ((-93086362251786267827501 : Int)/10^30,(105533604062317105755 : Int)/10^30)
theorem v1575_pg_checked : Scalar.distance (sourceCoefficient 17 80 1 2) v1575_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1575_mb : Scalar.QComplex := ((-861518246585302048163109 : Int)/10^30,(-431476588396795511920793991 : Int)/10^30)
theorem v1575_mb_checked : Scalar.distance (sourceCoefficient 17 80 3 1) v1575_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1575_mg : Scalar.QComplex := ((-93086236520732095873542 : Int)/10^30,(185862902936500130678 : Int)/10^30)
theorem v1575_mg_checked : Scalar.distance (sourceCoefficient 17 80 3 2) v1575_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1575_upper : Scalar.QComplex := ((999995911270101933447989359318 : Int)/10^30,(-2859622890945749279736344423 : Int)/10^30)
theorem v1575_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 80 5) 1) 14) v1575_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1575 : Material (17 : Basis) (80 : Basis) where
  plus := ![v1575_pa,v1575_pb,v1575_pg]
  minus := ![(Primitive.Addresses.material1575 1).one,v1575_mb,v1575_mg]
  upper := v1575_upper
  lower := (Primitive.Addresses.material1575 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1575_pa_checked.trans (by decide +kernel)
    · exact v1575_pb_checked.trans (by decide +kernel)
    · exact v1575_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 80 Primitive.Addresses.material1575
    · exact v1575_mb_checked.trans (by decide +kernel)
    · exact v1575_mg_checked.trans (by decide +kernel)
  upper_error := v1575_upper_checked
  lower_error := reuse_lower_error 17 80 Primitive.Addresses.material1575

def v1576_pa : Scalar.QComplex := ((999999327259477441210017309823 : Int)/10^30,(-1159948530124405680608545155 : Int)/10^30)
theorem v1576_pa_checked : Scalar.distance (sourceCoefficient 17 81 1 0) v1576_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1576_pb : Scalar.QComplex := ((-500491627695982001880820 : Int)/10^30,(-431477154371069068323188531 : Int)/10^30)
theorem v1576_pb_checked : Scalar.distance (sourceCoefficient 17 81 1 1) v1576_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1576_pg : Scalar.QComplex := ((-93086359037361429575046 : Int)/10^30,(107975457979486101810 : Int)/10^30)
theorem v1576_pg_checked : Scalar.distance (sourceCoefficient 17 81 1 2) v1576_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1576_mb : Scalar.QComplex := ((-872836792552662373463115 : Int)/10^30,(-431476561810671620363676694 : Int)/10^30)
theorem v1576_mb_checked : Scalar.distance (sourceCoefficient 17 81 3 1) v1576_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1576_mg : Scalar.QComplex := ((-93086231199098500999409 : Int)/10^30,(188304753170551452042 : Int)/10^30)
theorem v1576_mg_checked : Scalar.distance (sourceCoefficient 17 81 3 2) v1576_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1576_upper : Scalar.QComplex := ((999995835912014374806645444900 : Int)/10^30,(-2885854922136876007000286833 : Int)/10^30)
theorem v1576_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 81 5) 1) 14) v1576_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1576 : Material (17 : Basis) (81 : Basis) where
  plus := ![v1576_pa,v1576_pb,v1576_pg]
  minus := ![(Primitive.Addresses.material1576 1).one,v1576_mb,v1576_mg]
  upper := v1576_upper
  lower := (Primitive.Addresses.material1576 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1576_pa_checked.trans (by decide +kernel)
    · exact v1576_pb_checked.trans (by decide +kernel)
    · exact v1576_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 81 Primitive.Addresses.material1576
    · exact v1576_mb_checked.trans (by decide +kernel)
    · exact v1576_mg_checked.trans (by decide +kernel)
  upper_error := v1576_upper_checked
  lower_error := reuse_lower_error 17 81 Primitive.Addresses.material1576

def v1577_pa : Scalar.QComplex := ((999999315679884396184219106293 : Int)/10^30,(-1169888782283859212903813853 : Int)/10^30)
theorem v1577_pa_checked : Scalar.distance (sourceCoefficient 17 82 1 0) v1577_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1577_pb : Scalar.QComplex := ((-504780620565083350012208 : Int)/10^30,(-431477147894449992906419428 : Int)/10^30)
theorem v1577_pb_checked : Scalar.distance (sourceCoefficient 17 82 1 1) v1577_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1577_pg : Scalar.QComplex := ((-93086357799781018946440 : Int)/10^30,(108900760296606311896 : Int)/10^30)
theorem v1577_pg_checked : Scalar.distance (sourceCoefficient 17 82 1 2) v1577_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1577_mb : Scalar.QComplex := ((-877125778235745093780751 : Int)/10^30,(-431476551632847279521773499 : Int)/10^30)
theorem v1577_mb_checked : Scalar.distance (sourceCoefficient 17 82 3 1) v1577_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1577_mg : Scalar.QComplex := ((-93086229163024325573157 : Int)/10^30,(189230054075163165240 : Int)/10^30)
theorem v1577_mg_checked : Scalar.distance (sourceCoefficient 17 82 3 2) v1577_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1577_upper : Scalar.QComplex := ((999995807176465121639300919094 : Int)/10^30,(-2895795139506164508592614032 : Int)/10^30)
theorem v1577_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 82 5) 1) 14) v1577_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1577 : Material (17 : Basis) (82 : Basis) where
  plus := ![v1577_pa,v1577_pb,v1577_pg]
  minus := ![(Primitive.Addresses.material1577 1).one,v1577_mb,v1577_mg]
  upper := v1577_upper
  lower := (Primitive.Addresses.material1577 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1577_pa_checked.trans (by decide +kernel)
    · exact v1577_pb_checked.trans (by decide +kernel)
    · exact v1577_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 82 Primitive.Addresses.material1577
    · exact v1577_mb_checked.trans (by decide +kernel)
    · exact v1577_mg_checked.trans (by decide +kernel)
  upper_error := v1577_upper_checked
  lower_error := reuse_lower_error 17 82 Primitive.Addresses.material1577

def v1578_pa : Scalar.QComplex := ((999999299714053437290491163320 : Int)/10^30,(-1183457393709216751219506372 : Int)/10^30)
theorem v1578_pa_checked : Scalar.distance (sourceCoefficient 17 83 1 0) v1578_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1578_pb : Scalar.QComplex := ((-510635167911709965525571 : Int)/10^30,(-431477138961999996180286572 : Int)/10^30)
theorem v1578_pb_checked : Scalar.distance (sourceCoefficient 17 83 1 1) v1578_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1578_pg : Scalar.QComplex := ((-93086356093142020681161 : Int)/10^30,(110163813518048350470 : Int)/10^30)
theorem v1578_pg_checked : Scalar.distance (sourceCoefficient 17 83 1 2) v1578_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1578_mb : Scalar.QComplex := ((-882980315694154121552279 : Int)/10^30,(-431476537648189927640504950 : Int)/10^30)
theorem v1578_mb_checked : Scalar.distance (sourceCoefficient 17 83 3 1) v1578_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1578_mg : Scalar.QComplex := ((-93086226366427918468489 : Int)/10^30,(190493105353560173750 : Int)/10^30)
theorem v1578_mg_checked : Scalar.distance (sourceCoefficient 17 83 3 2) v1578_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1578_upper : Scalar.QComplex := ((999995767792465556621170227875 : Int)/10^30,(-2909363703167093383719980879 : Int)/10^30)
theorem v1578_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 83 5) 1) 14) v1578_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1578 : Material (17 : Basis) (83 : Basis) where
  plus := ![v1578_pa,v1578_pb,v1578_pg]
  minus := ![(Primitive.Addresses.material1578 1).one,v1578_mb,v1578_mg]
  upper := v1578_upper
  lower := (Primitive.Addresses.material1578 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1578_pa_checked.trans (by decide +kernel)
    · exact v1578_pb_checked.trans (by decide +kernel)
    · exact v1578_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 83 Primitive.Addresses.material1578
    · exact v1578_mb_checked.trans (by decide +kernel)
    · exact v1578_mg_checked.trans (by decide +kernel)
  upper_error := v1578_upper_checked
  lower_error := reuse_lower_error 17 83 Primitive.Addresses.material1578

def v1579_pa : Scalar.QComplex := ((999999257511100172947207088154 : Int)/10^30,(-1218596425550452375622822828 : Int)/10^30)
theorem v1579_pa_checked : Scalar.distance (sourceCoefficient 17 84 1 0) v1579_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1579_pb : Scalar.QComplex := ((-525796860854874694709959 : Int)/10^30,(-431477115337043880538158598 : Int)/10^30)
theorem v1579_pb_checked : Scalar.distance (sourceCoefficient 17 84 1 1) v1579_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1579_pg : Scalar.QComplex := ((-93086351580471385270402 : Int)/10^30,(113434779527559786813 : Int)/10^30)
theorem v1579_pg_checked : Scalar.distance (sourceCoefficient 17 84 1 2) v1579_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1579_mb : Scalar.QComplex := ((-898141982604654545123511 : Int)/10^30,(-431476500939384455999396959 : Int)/10^30)
theorem v1579_mb_checked : Scalar.distance (sourceCoefficient 17 84 3 1) v1579_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1579_mg : Scalar.QComplex := ((-93086219031062615963213 : Int)/10^30,(193764066250909959002 : Int)/10^30)
theorem v1579_mg_checked : Scalar.distance (sourceCoefficient 17 84 3 2) v1579_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1579_upper : Scalar.QComplex := ((999995664942793978713581613613 : Int)/10^30,(-2944502609834400088995545410 : Int)/10^30)
theorem v1579_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 84 5) 1) 14) v1579_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1579 : Material (17 : Basis) (84 : Basis) where
  plus := ![v1579_pa,v1579_pb,v1579_pg]
  minus := ![(Primitive.Addresses.material1579 1).one,v1579_mb,v1579_mg]
  upper := v1579_upper
  lower := (Primitive.Addresses.material1579 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1579_pa_checked.trans (by decide +kernel)
    · exact v1579_pb_checked.trans (by decide +kernel)
    · exact v1579_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 84 Primitive.Addresses.material1579
    · exact v1579_mb_checked.trans (by decide +kernel)
    · exact v1579_mg_checked.trans (by decide +kernel)
  upper_error := v1579_upper_checked
  lower_error := reuse_lower_error 17 84 Primitive.Addresses.material1579

def v1580_pa : Scalar.QComplex := ((999999158047757248125261670171 : Int)/10^30,(-1297653180406910728482272136 : Int)/10^30)
theorem v1580_pa_checked : Scalar.distance (sourceCoefficient 17 85 1 0) v1580_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1580_pb : Scalar.QComplex := ((-559908050062911292640499 : Int)/10^30,(-431477059588063555396988985 : Int)/10^30)
theorem v1580_pb_checked : Scalar.distance (sourceCoefficient 17 85 1 1) v1580_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1580_pg : Scalar.QComplex := ((-93086340937519352920125 : Int)/10^30,(120793888072698973959 : Int)/10^30)
theorem v1580_pg_checked : Scalar.distance (sourceCoefficient 17 85 1 2) v1580_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1580_mb : Scalar.QComplex := ((-932253111002677262811334 : Int)/10^30,(-431476415754004913147260101 : Int)/10^30)
theorem v1580_mb_checked : Scalar.distance (sourceCoefficient 17 85 3 1) v1580_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1580_mg : Scalar.QComplex := ((-93086202037535313960436 : Int)/10^30,(201123162871528443765 : Int)/10^30)
theorem v1580_mg_checked : Scalar.distance (sourceCoefficient 17 85 3 2) v1580_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1580_upper : Scalar.QComplex := ((999995429034812283386221783183 : Int)/10^30,(-3023559075280402097679664795 : Int)/10^30)
theorem v1580_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 85 5) 1) 14) v1580_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1580 : Material (17 : Basis) (85 : Basis) where
  plus := ![v1580_pa,v1580_pb,v1580_pg]
  minus := ![(Primitive.Addresses.material1580 1).one,v1580_mb,v1580_mg]
  upper := v1580_upper
  lower := (Primitive.Addresses.material1580 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1580_pa_checked.trans (by decide +kernel)
    · exact v1580_pb_checked.trans (by decide +kernel)
    · exact v1580_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 85 Primitive.Addresses.material1580
    · exact v1580_mb_checked.trans (by decide +kernel)
    · exact v1580_mg_checked.trans (by decide +kernel)
  upper_error := v1580_upper_checked
  lower_error := reuse_lower_error 17 85 Primitive.Addresses.material1580

def v1581_pa : Scalar.QComplex := ((999999139015591614325151074888 : Int)/10^30,(-1312237812089408668332025629 : Int)/10^30)
theorem v1581_pa_checked : Scalar.distance (sourceCoefficient 17 86 1 0) v1581_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1581_pb : Scalar.QComplex := ((-566200986119287900114664 : Int)/10^30,(-431477048910467648111756223 : Int)/10^30)
theorem v1581_pb_checked : Scalar.distance (sourceCoefficient 17 86 1 1) v1581_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1581_pg : Scalar.QComplex := ((-93086338899915460428813 : Int)/10^30,(122151518863991478904 : Int)/10^30)
theorem v1581_pg_checked : Scalar.distance (sourceCoefficient 17 86 1 2) v1581_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1581_mb : Scalar.QComplex := ((-938546035501621808191537 : Int)/10^30,(-431476399645892588284772667 : Int)/10^30)
theorem v1581_mb_checked : Scalar.distance (sourceCoefficient 17 86 3 1) v1581_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1581_mg : Scalar.QComplex := ((-93086198828357952697759 : Int)/10^30,(202480791398952569372 : Int)/10^30)
theorem v1581_mg_checked : Scalar.distance (sourceCoefficient 17 86 3 2) v1581_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1581_upper : Scalar.QComplex := ((999995384830923819220391336112 : Int)/10^30,(-3038143652393013078274058797 : Int)/10^30)
theorem v1581_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 86 5) 1) 14) v1581_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1581 : Material (17 : Basis) (86 : Basis) where
  plus := ![v1581_pa,v1581_pb,v1581_pg]
  minus := ![(Primitive.Addresses.material1581 1).one,v1581_mb,v1581_mg]
  upper := v1581_upper
  lower := (Primitive.Addresses.material1581 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1581_pa_checked.trans (by decide +kernel)
    · exact v1581_pb_checked.trans (by decide +kernel)
    · exact v1581_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 86 Primitive.Addresses.material1581
    · exact v1581_mb_checked.trans (by decide +kernel)
    · exact v1581_mg_checked.trans (by decide +kernel)
  upper_error := v1581_upper_checked
  lower_error := reuse_lower_error 17 86 Primitive.Addresses.material1581

def v1582_pa : Scalar.QComplex := ((999999137747823153593383542088 : Int)/10^30,(-1313203567697711045382103231 : Int)/10^30)
theorem v1582_pa_checked : Scalar.distance (sourceCoefficient 17 87 1 0) v1582_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1582_pb : Scalar.QComplex := ((-566617687642077387903720 : Int)/10^30,(-431477048199105658146480493 : Int)/10^30)
theorem v1582_pb_checked : Scalar.distance (sourceCoefficient 17 87 1 1) v1582_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1582_pg : Scalar.QComplex := ((-93086338764175259231247 : Int)/10^30,(122241417571961091180 : Int)/10^30)
theorem v1582_pg_checked : Scalar.distance (sourceCoefficient 17 87 1 2) v1582_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1582_mb : Scalar.QComplex := ((-938962736255380916060340 : Int)/10^30,(-431476398574936216564651298 : Int)/10^30)
theorem v1582_mb_checked : Scalar.distance (sourceCoefficient 17 87 3 1) v1582_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1582_mg : Scalar.QComplex := ((-93086198615039265952204 : Int)/10^30,(202570689956311103975 : Int)/10^30)
theorem v1582_mg_checked : Scalar.distance (sourceCoefficient 17 87 3 2) v1582_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1582_upper : Scalar.QComplex := ((999995381896350679415313345984 : Int)/10^30,(-3039109404374882570213927095 : Int)/10^30)
theorem v1582_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 87 5) 1) 14) v1582_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1582 : Material (17 : Basis) (87 : Basis) where
  plus := ![v1582_pa,v1582_pb,v1582_pg]
  minus := ![(Primitive.Addresses.material1582 1).one,v1582_mb,v1582_mg]
  upper := v1582_upper
  lower := (Primitive.Addresses.material1582 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1582_pa_checked.trans (by decide +kernel)
    · exact v1582_pb_checked.trans (by decide +kernel)
    · exact v1582_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 87 Primitive.Addresses.material1582
    · exact v1582_mb_checked.trans (by decide +kernel)
    · exact v1582_mg_checked.trans (by decide +kernel)
  upper_error := v1582_upper_checked
  lower_error := reuse_lower_error 17 87 Primitive.Addresses.material1582

def v1583_pa : Scalar.QComplex := ((999999122235938981592385279108 : Int)/10^30,(-1324963151022347645241976657 : Int)/10^30)
theorem v1583_pa_checked : Scalar.distance (sourceCoefficient 17 88 1 0) v1583_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1583_pb : Scalar.QComplex := ((-571691679652328875339396 : Int)/10^30,(-431477039494116465030642692 : Int)/10^30)
theorem v1583_pb_checked : Scalar.distance (sourceCoefficient 17 88 1 1) v1583_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1583_pg : Scalar.QComplex := ((-93086337103200458690683 : Int)/10^30,(123336074785358826036 : Int)/10^30)
theorem v1583_pg_checked : Scalar.distance (sourceCoefficient 17 88 1 2) v1583_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1583_mb : Scalar.QComplex := ((-944036718864339669689185 : Int)/10^30,(-431476385491323683984021846 : Int)/10^30)
theorem v1583_mb_checked : Scalar.distance (sourceCoefficient 17 88 3 1) v1583_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1583_mg : Scalar.QComplex := ((-93086196009425210236956 : Int)/10^30,(203665345328771484639 : Int)/10^30)
theorem v1583_mg_checked : Scalar.distance (sourceCoefficient 17 88 3 2) v1583_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1583_upper : Scalar.QComplex := ((999995346088515613286526205314 : Int)/10^30,(-3050868943412896331987093095 : Int)/10^30)
theorem v1583_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 88 5) 1) 14) v1583_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1583 : Material (17 : Basis) (88 : Basis) where
  plus := ![v1583_pa,v1583_pb,v1583_pg]
  minus := ![(Primitive.Addresses.material1583 1).one,v1583_mb,v1583_mg]
  upper := v1583_upper
  lower := (Primitive.Addresses.material1583 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1583_pa_checked.trans (by decide +kernel)
    · exact v1583_pb_checked.trans (by decide +kernel)
    · exact v1583_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 88 Primitive.Addresses.material1583
    · exact v1583_mb_checked.trans (by decide +kernel)
    · exact v1583_mg_checked.trans (by decide +kernel)
  upper_error := v1583_upper_checked
  lower_error := reuse_lower_error 17 88 Primitive.Addresses.material1583

def v1584_pa : Scalar.QComplex := ((999999100788529222211797517368 : Int)/10^30,(-1341052621254776574329258163 : Int)/10^30)
theorem v1584_pa_checked : Scalar.distance (sourceCoefficient 17 89 1 0) v1584_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1584_pb : Scalar.QComplex := ((-578633918994076608283526 : Int)/10^30,(-431477027455053927184839833 : Int)/10^30)
theorem v1584_pb_checked : Scalar.distance (sourceCoefficient 17 89 1 1) v1584_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1584_pg : Scalar.QComplex := ((-93086334806322769269699 : Int)/10^30,(124833785546990799069 : Int)/10^30)
theorem v1584_pg_checked : Scalar.distance (sourceCoefficient 17 89 1 2) v1584_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1584_mb : Scalar.QComplex := ((-950978945232005668776615 : Int)/10^30,(-431476367461425743756333782 : Int)/10^30)
theorem v1584_mb_checked : Scalar.distance (sourceCoefficient 17 89 3 1) v1584_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1584_mg : Scalar.QComplex := ((-93086192420091443148794 : Int)/10^30,(205163053550635293913 : Int)/10^30)
theorem v1584_mg_checked : Scalar.distance (sourceCoefficient 17 89 3 2) v1584_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1584_upper : Scalar.QComplex := ((999995296872171801468572245880 : Int)/10^30,(-3066958352665665800933931357 : Int)/10^30)
theorem v1584_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 17 89 5) 1) 14) v1584_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1584 : Material (17 : Basis) (89 : Basis) where
  plus := ![v1584_pa,v1584_pb,v1584_pg]
  minus := ![(Primitive.Addresses.material1584 1).one,v1584_mb,v1584_mg]
  upper := v1584_upper
  lower := (Primitive.Addresses.material1584 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1584_pa_checked.trans (by decide +kernel)
    · exact v1584_pb_checked.trans (by decide +kernel)
    · exact v1584_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 17 89 Primitive.Addresses.material1584
    · exact v1584_mb_checked.trans (by decide +kernel)
    · exact v1584_mg_checked.trans (by decide +kernel)
  upper_error := v1584_upper_checked
  lower_error := reuse_lower_error 17 89 Primitive.Addresses.material1584

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
