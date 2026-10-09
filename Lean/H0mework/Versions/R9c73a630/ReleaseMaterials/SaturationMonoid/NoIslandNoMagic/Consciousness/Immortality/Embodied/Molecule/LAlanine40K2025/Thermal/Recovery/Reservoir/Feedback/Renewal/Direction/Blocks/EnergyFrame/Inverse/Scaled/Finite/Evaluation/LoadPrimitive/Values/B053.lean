import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B035
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B036

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v849_pa : Scalar.QComplex := ((999999997903420302699033357664 : Int)/10^30,(-64754609026742543197364397 : Int)/10^30)
theorem v849_pa_checked : Scalar.distance (sourceCoefficient 9 22 1 0) v849_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v849_pb : Scalar.QComplex := ((-27940157873145900505276 : Int)/10^30,(-431477515415594999181629262 : Int)/10^30)
theorem v849_pb_checked : Scalar.distance (sourceCoefficient 9 22 1 1) v849_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v849_pg : Scalar.QComplex := ((-93086429196937756851338 : Int)/10^30,(6027775340980967696 : Int)/10^30)
theorem v849_pg_checked : Scalar.distance (sourceCoefficient 9 22 1 2) v849_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v849_mb : Scalar.QComplex := ((-400285810247500192711184 : Int)/10^30,(-431477330645698646810728013 : Int)/10^30)
theorem v849_mb_checked : Scalar.distance (sourceCoefficient 9 22 3 1) v849_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v849_mg : Scalar.QComplex := ((-93086389334907268509341 : Int)/10^30,(86357169036382303933 : Int)/10^30)
theorem v849_mg_checked : Scalar.distance (sourceCoefficient 9 22 3 2) v849_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v849_upper : Scalar.QComplex := ((999998396760310989087094247071 : Int)/10^30,(-1790663789672512865072756474 : Int)/10^30)
theorem v849_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 22 5) 1) 14) v849_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material849 : Material (9 : Basis) (22 : Basis) where
  plus := ![v849_pa,v849_pb,v849_pg]
  minus := ![(Primitive.Addresses.material849 1).one,v849_mb,v849_mg]
  upper := v849_upper
  lower := (Primitive.Addresses.material849 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v849_pa_checked.trans (by decide +kernel)
    · exact v849_pb_checked.trans (by decide +kernel)
    · exact v849_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 22 Primitive.Addresses.material849
    · exact v849_mb_checked.trans (by decide +kernel)
    · exact v849_mg_checked.trans (by decide +kernel)
  upper_error := v849_upper_checked
  lower_error := reuse_lower_error 9 22 Primitive.Addresses.material849

def v850_pa : Scalar.QComplex := ((999999997182746295535797465737 : Int)/10^30,(-75063355913464771184220988 : Int)/10^30)
theorem v850_pa_checked : Scalar.distance (sourceCoefficient 9 23 1 0) v850_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v850_pb : Scalar.QComplex := ((-32388150347236048192427 : Int)/10^30,(-431477514718745283797103661 : Int)/10^30)
theorem v850_pb_checked : Scalar.distance (sourceCoefficient 9 23 1 1) v850_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v850_pg : Scalar.QComplex := ((-93086429088226521496978 : Int)/10^30,(6987379777048268912 : Int)/10^30)
theorem v850_pg_checked : Scalar.distance (sourceCoefficient 9 23 1 2) v850_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v850_mb : Scalar.QComplex := ((-404733800464049539565380 : Int)/10^30,(-431477326110432015899830099 : Int)/10^30)
theorem v850_mb_checked : Scalar.distance (sourceCoefficient 9 23 3 1) v850_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v850_mg : Scalar.QComplex := ((-93086388398100664286498 : Int)/10^30,(87316773021332117573 : Int)/10^30)
theorem v850_mg_checked : Scalar.distance (sourceCoefficient 9 23 3 2) v850_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v850_upper : Scalar.QComplex := ((999998378247676131012734871431 : Int)/10^30,(-1800972519961749598432271818 : Int)/10^30)
theorem v850_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 23 5) 1) 14) v850_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material850 : Material (9 : Basis) (23 : Basis) where
  plus := ![v850_pa,v850_pb,v850_pg]
  minus := ![(Primitive.Addresses.material850 1).one,v850_mb,v850_mg]
  upper := v850_upper
  lower := (Primitive.Addresses.material850 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v850_pa_checked.trans (by decide +kernel)
    · exact v850_pb_checked.trans (by decide +kernel)
    · exact v850_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 23 Primitive.Addresses.material850
    · exact v850_mb_checked.trans (by decide +kernel)
    · exact v850_mg_checked.trans (by decide +kernel)
  upper_error := v850_upper_checked
  lower_error := reuse_lower_error 9 23 Primitive.Addresses.material850

def v851_pa : Scalar.QComplex := ((999999992060824091245636020128 : Int)/10^30,(-126009332013459280338927482 : Int)/10^30)
theorem v851_pa_checked : Scalar.distance (sourceCoefficient 9 24 1 0) v851_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v851_pb : Scalar.QComplex := ((-54370193293120306056675 : Int)/10^30,(-431477510377234604636320324 : Int)/10^30)
theorem v851_pb_checked : Scalar.distance (sourceCoefficient 9 24 1 1) v851_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v851_pg : Scalar.QComplex := ((-93086428381519708772553 : Int)/10^30,(11729758752998634090 : Int)/10^30)
theorem v851_pg_checked : Scalar.distance (sourceCoefficient 9 24 1 2) v851_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v851_mb : Scalar.QComplex := ((-426715831478486397951269 : Int)/10^30,(-431477302799409925446250762 : Int)/10^30)
theorem v851_mb_checked : Scalar.distance (sourceCoefficient 9 24 3 1) v851_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v851_mg : Scalar.QComplex := ((-93086383598934647276440 : Int)/10^30,(92059149621621902091 : Int)/10^30)
theorem v851_mg_checked : Scalar.distance (sourceCoefficient 9 24 3 2) v851_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v851_upper : Scalar.QComplex := ((999998285197628589481915854227 : Int)/10^30,(-1851918411343724173936351334 : Int)/10^30)
theorem v851_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 24 5) 1) 14) v851_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material851 : Material (9 : Basis) (24 : Basis) where
  plus := ![v851_pa,v851_pb,v851_pg]
  minus := ![(Primitive.Addresses.material851 1).one,v851_mb,v851_mg]
  upper := v851_upper
  lower := (Primitive.Addresses.material851 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v851_pa_checked.trans (by decide +kernel)
    · exact v851_pb_checked.trans (by decide +kernel)
    · exact v851_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 24 Primitive.Addresses.material851
    · exact v851_mb_checked.trans (by decide +kernel)
    · exact v851_mg_checked.trans (by decide +kernel)
  upper_error := v851_upper_checked
  lower_error := reuse_lower_error 9 24 Primitive.Addresses.material851

def v852_pa : Scalar.QComplex := ((999999988900442953284108386021 : Int)/10^30,(-148993670906624810881860767 : Int)/10^30)
theorem v852_pa_checked : Scalar.distance (sourceCoefficient 9 25 1 0) v852_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v852_pb : Scalar.QComplex := ((-64287418533660279414428 : Int)/10^30,(-431477507929767727631404687 : Int)/10^30)
theorem v852_pb_checked : Scalar.distance (sourceCoefficient 9 25 1 1) v852_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v852_pg : Scalar.QComplex := ((-93086427970418663325083 : Int)/10^30,(13869288768840755127 : Int)/10^30)
theorem v852_pg_checked : Scalar.distance (sourceCoefficient 9 25 1 2) v852_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v852_mb : Scalar.QComplex := ((-436633050914336489632982 : Int)/10^30,(-431477291793825232403323065 : Int)/10^30)
theorem v852_mb_checked : Scalar.distance (sourceCoefficient 9 25 3 1) v852_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v852_mg : Scalar.QComplex := ((-93086381341515712083757 : Int)/10^30,(94198678486057529960 : Int)/10^30)
theorem v852_mg_checked : Scalar.distance (sourceCoefficient 9 25 3 2) v852_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v852_upper : Scalar.QComplex := ((999998242368368351869444512276 : Int)/10^30,(-1874902710549885716630966531 : Int)/10^30)
theorem v852_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 25 5) 1) 14) v852_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material852 : Material (9 : Basis) (25 : Basis) where
  plus := ![v852_pa,v852_pb,v852_pg]
  minus := ![(Primitive.Addresses.material852 1).one,v852_mb,v852_mg]
  upper := v852_upper
  lower := (Primitive.Addresses.material852 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v852_pa_checked.trans (by decide +kernel)
    · exact v852_pb_checked.trans (by decide +kernel)
    · exact v852_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 25 Primitive.Addresses.material852
    · exact v852_mb_checked.trans (by decide +kernel)
    · exact v852_mg_checked.trans (by decide +kernel)
  upper_error := v852_upper_checked
  lower_error := reuse_lower_error 9 25 Primitive.Addresses.material852

def v853_pa : Scalar.QComplex := ((999999987779277074078021697402 : Int)/10^30,(-156337601691013182092843063 : Int)/10^30)
theorem v853_pa_checked : Scalar.distance (sourceCoefficient 9 26 1 0) v853_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v853_pb : Scalar.QComplex := ((-67456159465443890231270 : Int)/10^30,(-431477507083687503851905528 : Int)/10^30)
theorem v853_pb_checked : Scalar.distance (sourceCoefficient 9 26 1 1) v853_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v853_pg : Scalar.QComplex := ((-93086427826969845397950 : Int)/10^30,(14552909054299126750 : Int)/10^30)
theorem v853_pg_checked : Scalar.distance (sourceCoefficient 9 26 1 2) v853_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v853_mb : Scalar.QComplex := ((-439801789936123905849027 : Int)/10^30,(-431477288213264614322648224 : Int)/10^30)
theorem v853_mb_checked : Scalar.distance (sourceCoefficient 9 26 3 1) v853_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v853_mg : Scalar.QComplex := ((-93086380608133430333311 : Int)/10^30,(94882298393182957140 : Int)/10^30)
theorem v853_mg_checked : Scalar.distance (sourceCoefficient 9 26 3 2) v853_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v853_upper : Scalar.QComplex := ((999998228572245844850312948413 : Int)/10^30,(-1882246628461321267069608623 : Int)/10^30)
theorem v853_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 26 5) 1) 14) v853_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material853 : Material (9 : Basis) (26 : Basis) where
  plus := ![v853_pa,v853_pb,v853_pg]
  minus := ![(Primitive.Addresses.material853 1).one,v853_mb,v853_mg]
  upper := v853_upper
  lower := (Primitive.Addresses.material853 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v853_pa_checked.trans (by decide +kernel)
    · exact v853_pb_checked.trans (by decide +kernel)
    · exact v853_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 26 Primitive.Addresses.material853
    · exact v853_mb_checked.trans (by decide +kernel)
    · exact v853_mg_checked.trans (by decide +kernel)
  upper_error := v853_upper_checked
  lower_error := reuse_lower_error 9 26 Primitive.Addresses.material853

def v854_pa : Scalar.QComplex := ((999999986977790181508186237060 : Int)/10^30,(-161382835107720421312003463 : Int)/10^30)
theorem v854_pa_checked : Scalar.distance (sourceCoefficient 9 27 1 0) v854_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v854_pb : Scalar.QComplex := ((-69633064188447669440520 : Int)/10^30,(-431477506484455787933630535 : Int)/10^30)
theorem v854_pb_checked : Scalar.distance (sourceCoefficient 9 27 1 1) v854_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v854_pg : Scalar.QComplex := ((-93086427725027311991158 : Int)/10^30,(15022551811941638979 : Int)/10^30)
theorem v854_pg_checked : Scalar.distance (sourceCoefficient 9 27 1 2) v854_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v854_mb : Scalar.QComplex := ((-441978693331456584780407 : Int)/10^30,(-431477285735462389722620046 : Int)/10^30)
theorem v854_mb_checked : Scalar.distance (sourceCoefficient 9 27 3 1) v854_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v854_mg : Scalar.QComplex := ((-93086380100910386963503 : Int)/10^30,(95351940887984191956 : Int)/10^30)
theorem v854_mg_checked : Scalar.distance (sourceCoefficient 9 27 3 2) v854_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v854_upper : Scalar.QComplex := ((999998219063144968764567303462 : Int)/10^30,(-1887291852980452320599564147 : Int)/10^30)
theorem v854_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 27 5) 1) 14) v854_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material854 : Material (9 : Basis) (27 : Basis) where
  plus := ![v854_pa,v854_pb,v854_pg]
  minus := ![(Primitive.Addresses.material854 1).one,v854_mb,v854_mg]
  upper := v854_upper
  lower := (Primitive.Addresses.material854 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v854_pa_checked.trans (by decide +kernel)
    · exact v854_pb_checked.trans (by decide +kernel)
    · exact v854_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 27 Primitive.Addresses.material854
    · exact v854_mb_checked.trans (by decide +kernel)
    · exact v854_mg_checked.trans (by decide +kernel)
  upper_error := v854_upper_checked
  lower_error := reuse_lower_error 9 27 Primitive.Addresses.material854

def v855_pa : Scalar.QComplex := ((999999985857841316891552061704 : Int)/10^30,(-168179419567960941569769065 : Int)/10^30)
theorem v855_pa_checked : Scalar.distance (sourceCoefficient 9 28 1 0) v855_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v855_pb : Scalar.QComplex := ((-72565637483766414037029 : Int)/10^30,(-431477505654061531888308005 : Int)/10^30)
theorem v855_pb_checked : Scalar.distance (sourceCoefficient 9 28 1 1) v855_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v855_pg : Scalar.QComplex := ((-93086427583327173513155 : Int)/10^30,(15655221582017621018 : Int)/10^30)
theorem v855_pg_checked : Scalar.distance (sourceCoefficient 9 28 1 2) v855_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v855_mb : Scalar.QComplex := ((-444911264818251422911012 : Int)/10^30,(-431477282374389767209201319 : Int)/10^30)
theorem v855_mb_checked : Scalar.distance (sourceCoefficient 9 28 3 1) v855_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v855_mg : Scalar.QComplex := ((-93086379413244784060049 : Int)/10^30,(95984610300207466589 : Int)/10^30)
theorem v855_mg_checked : Scalar.distance (sourceCoefficient 9 28 3 2) v855_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v855_upper : Scalar.QComplex := ((999998206212909575130834597763 : Int)/10^30,(-1894088425385048530862138347 : Int)/10^30)
theorem v855_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 28 5) 1) 14) v855_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material855 : Material (9 : Basis) (28 : Basis) where
  plus := ![v855_pa,v855_pb,v855_pg]
  minus := ![(Primitive.Addresses.material855 1).one,v855_mb,v855_mg]
  upper := v855_upper
  lower := (Primitive.Addresses.material855 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v855_pa_checked.trans (by decide +kernel)
    · exact v855_pb_checked.trans (by decide +kernel)
    · exact v855_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 28 Primitive.Addresses.material855
    · exact v855_mb_checked.trans (by decide +kernel)
    · exact v855_mg_checked.trans (by decide +kernel)
  upper_error := v855_upper_checked
  lower_error := reuse_lower_error 9 28 Primitive.Addresses.material855

def v856_pa : Scalar.QComplex := ((999999983448049012471771877190 : Int)/10^30,(-181944776514989225320954189 : Int)/10^30)
theorem v856_pa_checked : Scalar.distance (sourceCoefficient 9 29 1 0) v856_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v856_pb : Scalar.QComplex := ((-78505079316072456690476 : Int)/10^30,(-431477503890817761685433608 : Int)/10^30)
theorem v856_pb_checked : Scalar.distance (sourceCoefficient 9 29 1 1) v856_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v856_pg : Scalar.QComplex := ((-93086427280967671112024 : Int)/10^30,(16936589488548058167 : Int)/10^30)
theorem v856_pg_checked : Scalar.distance (sourceCoefficient 9 29 1 2) v856_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v856_mb : Scalar.QComplex := ((-450850702917431865361844 : Int)/10^30,(-431477275485675854792418360 : Int)/10^30)
theorem v856_mb_checked : Scalar.distance (sourceCoefficient 9 29 3 1) v856_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v856_mg : Scalar.QComplex := ((-93086378005122601573601 : Int)/10^30,(97265977468703437925 : Int)/10^30)
theorem v856_mg_checked : Scalar.distance (sourceCoefficient 9 29 3 2) v856_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v856_upper : Scalar.QComplex := ((999998180045363552670073611615 : Int)/10^30,(-1907853757671111731650807088 : Int)/10^30)
theorem v856_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 29 5) 1) 14) v856_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material856 : Material (9 : Basis) (29 : Basis) where
  plus := ![v856_pa,v856_pb,v856_pg]
  minus := ![(Primitive.Addresses.material856 1).one,v856_mb,v856_mg]
  upper := v856_upper
  lower := (Primitive.Addresses.material856 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v856_pa_checked.trans (by decide +kernel)
    · exact v856_pb_checked.trans (by decide +kernel)
    · exact v856_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 29 Primitive.Addresses.material856
    · exact v856_mb_checked.trans (by decide +kernel)
    · exact v856_mg_checked.trans (by decide +kernel)
  upper_error := v856_upper_checked
  lower_error := reuse_lower_error 9 29 Primitive.Addresses.material856

def v857_pa : Scalar.QComplex := ((999999982485366028942347310494 : Int)/10^30,(-187161074038788584418417404 : Int)/10^30)
theorem v857_pa_checked : Scalar.distance (sourceCoefficient 9 30 1 0) v857_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v857_pb : Scalar.QComplex := ((-80755794335803087014847 : Int)/10^30,(-431477503194165826511287226 : Int)/10^30)
theorem v857_pb_checked : Scalar.distance (sourceCoefficient 9 30 1 1) v857_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v857_pg : Scalar.QComplex := ((-93086427161013894227716 : Int)/10^30,(17422155991031507280 : Int)/10^30)
theorem v857_pg_checked : Scalar.distance (sourceCoefficient 9 30 1 2) v857_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v857_mb : Scalar.QComplex := ((-453101416497939187065715 : Int)/10^30,(-431477272846758485427607278 : Int)/10^30)
theorem v857_mb_checked : Scalar.distance (sourceCoefficient 9 30 3 1) v857_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v857_mg : Scalar.QComplex := ((-93086377466146846813802 : Int)/10^30,(97751543686873579745 : Int)/10^30)
theorem v857_mg_checked : Scalar.distance (sourceCoefficient 9 30 3 2) v857_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v857_upper : Scalar.QComplex := ((999998170079825695680951082088 : Int)/10^30,(-1913070045764345182745828481 : Int)/10^30)
theorem v857_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 30 5) 1) 14) v857_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material857 : Material (9 : Basis) (30 : Basis) where
  plus := ![v857_pa,v857_pb,v857_pg]
  minus := ![(Primitive.Addresses.material857 1).one,v857_mb,v857_mg]
  upper := v857_upper
  lower := (Primitive.Addresses.material857 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v857_pa_checked.trans (by decide +kernel)
    · exact v857_pb_checked.trans (by decide +kernel)
    · exact v857_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 30 Primitive.Addresses.material857
    · exact v857_mb_checked.trans (by decide +kernel)
    · exact v857_mg_checked.trans (by decide +kernel)
  upper_error := v857_upper_checked
  lower_error := reuse_lower_error 9 30 Primitive.Addresses.material857

def v858_pa : Scalar.QComplex := ((999999980347250624588420424187 : Int)/10^30,(-198256143321190935394425158 : Int)/10^30)
theorem v858_pa_checked : Scalar.distance (sourceCoefficient 9 31 1 0) v858_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v858_pb : Scalar.QComplex := ((-85543067090195962849773 : Int)/10^30,(-431477501660328588971908442 : Int)/10^30)
theorem v858_pb_checked : Scalar.distance (sourceCoefficient 9 31 1 1) v858_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v858_pg : Scalar.QComplex := ((-93086426896045049750637 : Int)/10^30,(18454956354650502017 : Int)/10^30)
theorem v858_pg_checked : Scalar.distance (sourceCoefficient 9 31 1 2) v858_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v858_mb : Scalar.QComplex := ((-457888686146179172735163 : Int)/10^30,(-431477267181721042725890192 : Int)/10^30)
theorem v858_mb_checked : Scalar.distance (sourceCoefficient 9 31 3 1) v858_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v858_mg : Scalar.QComplex := ((-93086376309917902795178 : Int)/10^30,(98784343437277618768 : Int)/10^30)
theorem v858_mg_checked : Scalar.distance (sourceCoefficient 9 31 3 2) v858_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v858_upper : Scalar.QComplex := ((999998148792630431194965889228 : Int)/10^30,(-1924165094831751936373976826 : Int)/10^30)
theorem v858_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 31 5) 1) 14) v858_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material858 : Material (9 : Basis) (31 : Basis) where
  plus := ![v858_pa,v858_pb,v858_pg]
  minus := ![(Primitive.Addresses.material858 1).one,v858_mb,v858_mg]
  upper := v858_upper
  lower := (Primitive.Addresses.material858 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v858_pa_checked.trans (by decide +kernel)
    · exact v858_pb_checked.trans (by decide +kernel)
    · exact v858_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 31 Primitive.Addresses.material858
    · exact v858_mb_checked.trans (by decide +kernel)
    · exact v858_mg_checked.trans (by decide +kernel)
  upper_error := v858_upper_checked
  lower_error := reuse_lower_error 9 31 Primitive.Addresses.material858

def v859_pa : Scalar.QComplex := ((999999979388955909832342729542 : Int)/10^30,(-203032233291958289620053228 : Int)/10^30)
theorem v859_pa_checked : Scalar.distance (sourceCoefficient 9 32 1 0) v859_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v859_pb : Scalar.QComplex := ((-87603842444454625196009 : Int)/10^30,(-431477500978253698811007484 : Int)/10^30)
theorem v859_pb_checked : Scalar.distance (sourceCoefficient 9 32 1 1) v859_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v859_pg : Scalar.QComplex := ((-93086426777867933869514 : Int)/10^30,(18899545507418241279 : Int)/10^30)
theorem v859_pg_checked : Scalar.distance (sourceCoefficient 9 32 1 2) v859_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v859_mb : Scalar.QComplex := ((-459949460144517077908354 : Int)/10^30,(-431477264721290089683960358 : Int)/10^30)
theorem v859_mb_checked : Scalar.distance (sourceCoefficient 9 32 3 1) v859_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v859_mg : Scalar.QComplex := ((-93086375808080415630369 : Int)/10^30,(99228932322522969221 : Int)/10^30)
theorem v859_mg_checked : Scalar.distance (sourceCoefficient 9 32 3 2) v859_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v859_upper : Scalar.QComplex := ((999998139591239137659366300073 : Int)/10^30,(-1928941176035164576228860269 : Int)/10^30)
theorem v859_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 32 5) 1) 14) v859_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material859 : Material (9 : Basis) (32 : Basis) where
  plus := ![v859_pa,v859_pb,v859_pg]
  minus := ![(Primitive.Addresses.material859 1).one,v859_mb,v859_mg]
  upper := v859_upper
  lower := (Primitive.Addresses.material859 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v859_pa_checked.trans (by decide +kernel)
    · exact v859_pb_checked.trans (by decide +kernel)
    · exact v859_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 32 Primitive.Addresses.material859
    · exact v859_mb_checked.trans (by decide +kernel)
    · exact v859_mg_checked.trans (by decide +kernel)
  upper_error := v859_upper_checked
  lower_error := reuse_lower_error 9 32 Primitive.Addresses.material859

def v860_pa : Scalar.QComplex := ((999999978015397540381545989899 : Int)/10^30,(-209688350739649251295216594 : Int)/10^30)
theorem v860_pa_checked : Scalar.distance (sourceCoefficient 9 33 1 0) v860_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v860_pb : Scalar.QComplex := ((-90475807346558467355927 : Int)/10^30,(-431477500005802901299895557 : Int)/10^30)
theorem v860_pb_checked : Scalar.distance (sourceCoefficient 9 33 1 1) v860_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v860_pg : Scalar.QComplex := ((-93086426609040441868706 : Int)/10^30,(19519139701017617766 : Int)/10^30)
theorem v860_pg_checked : Scalar.distance (sourceCoefficient 9 33 1 2) v860_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v860_mb : Scalar.QComplex := ((-462821423138075891040831 : Int)/10^30,(-431477261270463292242656582 : Int)/10^30)
theorem v860_mb_checked : Scalar.distance (sourceCoefficient 9 33 3 1) v860_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v860_mg : Scalar.QComplex := ((-93086375104571102902069 : Int)/10^30,(99848526139728588689 : Int)/10^30)
theorem v860_mg_checked : Scalar.distance (sourceCoefficient 9 33 3 2) v860_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v860_upper : Scalar.QComplex := ((999998126729827937505740416191 : Int)/10^30,(-1935597281198713344617805782 : Int)/10^30)
theorem v860_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 33 5) 1) 14) v860_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material860 : Material (9 : Basis) (33 : Basis) where
  plus := ![v860_pa,v860_pb,v860_pg]
  minus := ![(Primitive.Addresses.material860 1).one,v860_mb,v860_mg]
  upper := v860_upper
  lower := (Primitive.Addresses.material860 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v860_pa_checked.trans (by decide +kernel)
    · exact v860_pb_checked.trans (by decide +kernel)
    · exact v860_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 33 Primitive.Addresses.material860
    · exact v860_mb_checked.trans (by decide +kernel)
    · exact v860_mg_checked.trans (by decide +kernel)
  upper_error := v860_upper_checked
  lower_error := reuse_lower_error 9 33 Primitive.Addresses.material860

def v861_pa : Scalar.QComplex := ((999999974494687887101435471730 : Int)/10^30,(-225855315578970120196115000 : Int)/10^30)
theorem v861_pa_checked : Scalar.distance (sourceCoefficient 9 34 1 0) v861_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v861_pb : Scalar.QComplex := ((-97451488857130135574460 : Int)/10^30,(-431477497537690967314111768 : Int)/10^30)
theorem v861_pb_checked : Scalar.distance (sourceCoefficient 9 34 1 1) v861_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v861_pg : Scalar.QComplex := ((-93086426178941578990715 : Int)/10^30,(21024064696988688021 : Int)/10^30)
theorem v861_pg_checked : Scalar.distance (sourceCoefficient 9 34 1 2) v861_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v861_mb : Scalar.QComplex := ((-469797099921413089084578 : Int)/10^30,(-431477252782653306656979402 : Int)/10^30)
theorem v861_mb_checked : Scalar.distance (sourceCoefficient 9 34 3 1) v861_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v861_mg : Scalar.QComplex := ((-93086373375789907952240 : Int)/10^30,(101353450204191356744 : Int)/10^30)
theorem v861_mg_checked : Scalar.distance (sourceCoefficient 9 34 3 2) v861_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v861_upper : Scalar.QComplex := ((999998095306408870834605557572 : Int)/10^30,(-1951764215882813725168441367 : Int)/10^30)
theorem v861_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 34 5) 1) 14) v861_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material861 : Material (9 : Basis) (34 : Basis) where
  plus := ![v861_pa,v861_pb,v861_pg]
  minus := ![(Primitive.Addresses.material861 1).one,v861_mb,v861_mg]
  upper := v861_upper
  lower := (Primitive.Addresses.material861 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v861_pa_checked.trans (by decide +kernel)
    · exact v861_pb_checked.trans (by decide +kernel)
    · exact v861_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 34 Primitive.Addresses.material861
    · exact v861_mb_checked.trans (by decide +kernel)
    · exact v861_mg_checked.trans (by decide +kernel)
  upper_error := v861_upper_checked
  lower_error := reuse_lower_error 9 34 Primitive.Addresses.material861

def v862_pa : Scalar.QComplex := ((999999961575250828175123938278 : Int)/10^30,(-277217418044372535068879585 : Int)/10^30)
theorem v862_pa_checked : Scalar.distance (sourceCoefficient 9 35 1 0) v862_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v862_pb : Scalar.QComplex := ((-119613079957467960944316 : Int)/10^30,(-431477488698850863369828844 : Int)/10^30)
theorem v862_pb_checked : Scalar.distance (sourceCoefficient 9 35 1 1) v862_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v862_pg : Scalar.QComplex := ((-93086424624189195402752 : Int)/10^30,(25805179280857370935 : Int)/10^30)
theorem v862_pg_checked : Scalar.distance (sourceCoefficient 9 35 1 2) v862_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v862_mb : Scalar.QComplex := ((-491958675142456789927022 : Int)/10^30,(-431477224819361495236444468 : Int)/10^30)
theorem v862_mb_checked : Scalar.distance (sourceCoefficient 9 35 3 1) v862_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v862_mg : Scalar.QComplex := ((-93086367695151550798278 : Int)/10^30,(106134561666151288763 : Int)/10^30)
theorem v862_mg_checked : Scalar.distance (sourceCoefficient 9 35 3 2) v862_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v862_upper : Scalar.QComplex := ((999997993740661732144984332289 : Int)/10^30,(-2003126219552621612671960908 : Int)/10^30)
theorem v862_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 35 5) 1) 14) v862_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material862 : Material (9 : Basis) (35 : Basis) where
  plus := ![v862_pa,v862_pb,v862_pg]
  minus := ![(Primitive.Addresses.material862 1).one,v862_mb,v862_mg]
  upper := v862_upper
  lower := (Primitive.Addresses.material862 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v862_pa_checked.trans (by decide +kernel)
    · exact v862_pb_checked.trans (by decide +kernel)
    · exact v862_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 35 Primitive.Addresses.material862
    · exact v862_mb_checked.trans (by decide +kernel)
    · exact v862_mg_checked.trans (by decide +kernel)
  upper_error := v862_upper_checked
  lower_error := reuse_lower_error 9 35 Primitive.Addresses.material862

def v863_pa : Scalar.QComplex := ((999999956969267305687317054313 : Int)/10^30,(-293362341715806137110157284 : Int)/10^30)
theorem v863_pa_checked : Scalar.distance (sourceCoefficient 9 36 1 0) v863_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v863_pb : Scalar.QComplex := ((-126579251022109823532959 : Int)/10^30,(-431477485606980740353137882 : Int)/10^30)
theorem v863_pb_checked : Scalar.distance (sourceCoefficient 9 36 1 1) v863_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v863_pg : Scalar.QComplex := ((-93086424076293784969876 : Int)/10^30,(27308052524057649563 : Int)/10^30)
theorem v863_pg_checked : Scalar.distance (sourceCoefficient 9 36 1 2) v863_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v863_mb : Scalar.QComplex := ((-498924840945130131901695 : Int)/10^30,(-431477215716000639376379156 : Int)/10^30)
theorem v863_mb_checked : Scalar.distance (sourceCoefficient 9 36 3 1) v863_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v863_mg : Scalar.QComplex := ((-93086365850344422388280 : Int)/10^30,(107637433876954111337 : Int)/10^30)
theorem v863_mg_checked : Scalar.distance (sourceCoefficient 9 36 3 2) v863_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v863_upper : Scalar.QComplex := ((999997961270011468868387634315 : Int)/10^30,(-2019271111228578213817442932 : Int)/10^30)
theorem v863_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 36 5) 1) 14) v863_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material863 : Material (9 : Basis) (36 : Basis) where
  plus := ![v863_pa,v863_pb,v863_pg]
  minus := ![(Primitive.Addresses.material863 1).one,v863_mb,v863_mg]
  upper := v863_upper
  lower := (Primitive.Addresses.material863 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v863_pa_checked.trans (by decide +kernel)
    · exact v863_pb_checked.trans (by decide +kernel)
    · exact v863_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 36 Primitive.Addresses.material863
    · exact v863_mb_checked.trans (by decide +kernel)
    · exact v863_mg_checked.trans (by decide +kernel)
  upper_error := v863_upper_checked
  lower_error := reuse_lower_error 9 36 Primitive.Addresses.material863

def v864_pa : Scalar.QComplex := ((999999954923046641714001028241 : Int)/10^30,(-300256398240970501851485741 : Int)/10^30)
theorem v864_pa_checked : Scalar.distance (sourceCoefficient 9 37 1 0) v864_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v864_pb : Scalar.QComplex := ((-129553881180181202291583 : Int)/10^30,(-431477484241030550937506577 : Int)/10^30)
theorem v864_pb_checked : Scalar.distance (sourceCoefficient 9 37 1 1) v864_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v864_pg : Scalar.QComplex := ((-93086423833711889604592 : Int)/10^30,(27949795605334398085 : Int)/10^30)
theorem v864_pg_checked : Scalar.distance (sourceCoefficient 9 37 1 2) v864_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v864_mb : Scalar.QComplex := ((-501899468816857262143295 : Int)/10^30,(-431477211783079104519861934 : Int)/10^30)
theorem v864_mb_checked : Scalar.distance (sourceCoefficient 9 37 3 1) v864_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v864_mg : Scalar.QComplex := ((-93086365053967241240938 : Int)/10^30,(108279176509943331375 : Int)/10^30)
theorem v864_mg_checked : Scalar.distance (sourceCoefficient 9 37 3 2) v864_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v864_upper : Scalar.QComplex := ((999997947325277713989110428987 : Int)/10^30,(-2026165153954263982764162090 : Int)/10^30)
theorem v864_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 37 5) 1) 14) v864_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material864 : Material (9 : Basis) (37 : Basis) where
  plus := ![v864_pa,v864_pb,v864_pg]
  minus := ![(Primitive.Addresses.material864 1).one,v864_mb,v864_mg]
  upper := v864_upper
  lower := (Primitive.Addresses.material864 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v864_pa_checked.trans (by decide +kernel)
    · exact v864_pb_checked.trans (by decide +kernel)
    · exact v864_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 37 Primitive.Addresses.material864
    · exact v864_mb_checked.trans (by decide +kernel)
    · exact v864_mg_checked.trans (by decide +kernel)
  upper_error := v864_upper_checked
  lower_error := reuse_lower_error 9 37 Primitive.Addresses.material864

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
