import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B020
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B021

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v497_pa : Scalar.QComplex := ((999992835648326349933750836312 : Int)/10^30,(3785320596642407086278052178 : Int)/10^30)
theorem v497_pa_checked : Scalar.distance (sourceCoefficient 5 28 1 0) v497_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v497_pb : Scalar.QComplex := ((1633275685758677322311646 : Int)/10^30,(-431473092621532644664193268 : Int)/10^30)
theorem v497_pb_checked : Scalar.distance (sourceCoefficient 5 28 1 1) v497_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v497_pg : Scalar.QComplex := ((-93085618758439358486153 : Int)/10^30,(-352361434378755434790 : Int)/10^30)
theorem v497_pg_checked : Scalar.distance (sourceCoefficient 5 28 1 2) v497_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v497_mb : Scalar.QComplex := ((1260933231509823693190303 : Int)/10^30,(-431474341407737770709618851 : Int)/10^30)
theorem v497_mb_checked : Scalar.distance (sourceCoefficient 5 28 3 1) v497_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v497_mg : Scalar.QComplex := ((-93085888170457370754113 : Int)/10^30,(-272032606610595446657 : Int)/10^30)
theorem v497_mg_checked : Scalar.distance (sourceCoefficient 5 28 3 2) v497_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v497_upper : Scalar.QComplex := ((999997879396413264635743961592 : Int)/10^30,(2059418043164416979461762744 : Int)/10^30)
theorem v497_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 28 5) 1) 14) v497_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material497 : Material (5 : Basis) (28 : Basis) where
  plus := ![v497_pa,v497_pb,v497_pg]
  minus := ![(Primitive.Addresses.material497 1).one,v497_mb,v497_mg]
  upper := v497_upper
  lower := (Primitive.Addresses.material497 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v497_pa_checked.trans (by decide +kernel)
    · exact v497_pb_checked.trans (by decide +kernel)
    · exact v497_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 28 Primitive.Addresses.material497
    · exact v497_mb_checked.trans (by decide +kernel)
    · exact v497_mg_checked.trans (by decide +kernel)
  upper_error := v497_upper_checked
  lower_error := reuse_lower_error 5 28 Primitive.Addresses.material497

def v498_pa : Scalar.QComplex := ((999992887659874468790001469262 : Int)/10^30,(3771555337746001938642237817 : Int)/10^30)
theorem v498_pa_checked : Scalar.distance (sourceCoefficient 5 29 1 0) v498_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v498_pb : Scalar.QComplex := ((1627336272130768942723086 : Int)/10^30,(-431473106512668187519198338 : Int)/10^30)
theorem v498_pb_checked : Scalar.distance (sourceCoefficient 5 29 1 1) v498_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v498_pg : Scalar.QComplex := ((-93085622677651709196204 : Int)/10^30,(-351080074078205730316 : Int)/10^30)
theorem v498_pg_checked : Scalar.distance (sourceCoefficient 5 29 1 2) v498_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v498_mb : Scalar.QComplex := ((1254993808106006111920836 : Int)/10^30,(-431474350173421681634760939 : Int)/10^30)
theorem v498_mb_checked : Scalar.distance (sourceCoefficient 5 29 3 1) v498_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v498_mg : Scalar.QComplex := ((-93085890983912033113522 : Int)/10^30,(-270751243405050999245 : Int)/10^30)
theorem v498_mg_checked : Scalar.distance (sourceCoefficient 5 29 3 2) v498_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v498_upper : Scalar.QComplex := ((999997907650295837737682926456 : Int)/10^30,(2045652715002534374765670470 : Int)/10^30)
theorem v498_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 29 5) 1) 14) v498_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material498 : Material (5 : Basis) (29 : Basis) where
  plus := ![v498_pa,v498_pb,v498_pg]
  minus := ![(Primitive.Addresses.material498 1).one,v498_mb,v498_mg]
  upper := v498_upper
  lower := (Primitive.Addresses.material498 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v498_pa_checked.trans (by decide +kernel)
    · exact v498_pb_checked.trans (by decide +kernel)
    · exact v498_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 29 Primitive.Addresses.material498
    · exact v498_mb_checked.trans (by decide +kernel)
    · exact v498_mg_checked.trans (by decide +kernel)
  upper_error := v498_upper_checked
  lower_error := reuse_lower_error 5 29 Primitive.Addresses.material498

def v499_pa : Scalar.QComplex := ((999992907319824789289076659569 : Int)/10^30,(3766339077182158597852484159 : Int)/10^30)
theorem v499_pa_checked : Scalar.distance (sourceCoefficient 5 30 1 0) v499_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v499_pb : Scalar.QComplex := ((1625085567742620813908545 : Int)/10^30,(-431473111748147291872739866 : Int)/10^30)
theorem v499_pb_checked : Scalar.distance (sourceCoefficient 5 30 1 1) v499_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v499_pg : Scalar.QComplex := ((-93085624157436699926880 : Int)/10^30,(-350594510442779145069 : Int)/10^30)
theorem v499_pg_checked : Scalar.distance (sourceCoefficient 5 30 1 2) v499_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v499_mb : Scalar.QComplex := ((1252743100037915419254431 : Int)/10^30,(-431474353466642317571010071 : Int)/10^30)
theorem v499_mb_checked : Scalar.distance (sourceCoefficient 5 30 3 1) v499_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v499_mg : Scalar.QComplex := ((-93085892044676924453799 : Int)/10^30,(-270265678673434146864 : Int)/10^30)
theorem v499_mg_checked : Scalar.distance (sourceCoefficient 5 30 3 2) v499_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v499_upper : Scalar.QComplex := ((999997918307424359318365064222 : Int)/10^30,(2040436428276407682391201939 : Int)/10^30)
theorem v499_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 30 5) 1) 14) v499_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material499 : Material (5 : Basis) (30 : Basis) where
  plus := ![v499_pa,v499_pb,v499_pg]
  minus := ![(Primitive.Addresses.material499 1).one,v499_mb,v499_mg]
  upper := v499_upper
  lower := (Primitive.Addresses.material499 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v499_pa_checked.trans (by decide +kernel)
    · exact v499_pb_checked.trans (by decide +kernel)
    · exact v499_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 30 Primitive.Addresses.material499
    · exact v499_mb_checked.trans (by decide +kernel)
    · exact v499_mg_checked.trans (by decide +kernel)
  upper_error := v499_upper_checked
  lower_error := reuse_lower_error 5 30 Primitive.Addresses.material499

def v500_pa : Scalar.QComplex := ((999992949046068720009964397488 : Int)/10^30,(3755244086155870512758232738 : Int)/10^30)
theorem v500_pa_checked : Scalar.distance (sourceCoefficient 5 31 1 0) v500_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v500_pb : Scalar.QComplex := ((1620298317498707365225714 : Int)/10^30,(-431473122831957990190769395 : Int)/10^30)
theorem v500_pb_checked : Scalar.distance (sourceCoefficient 5 31 1 1) v500_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v500_pg : Scalar.QComplex := ((-93085627295113625686612 : Int)/10^30,(-349561716149641634310 : Int)/10^30)
theorem v500_pg_checked : Scalar.distance (sourceCoefficient 5 31 1 2) v500_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v500_mb : Scalar.QComplex := ((1247955842011684588179432 : Int)/10^30,(-431474360419267538129631054 : Int)/10^30)
theorem v500_mb_checked : Scalar.distance (sourceCoefficient 5 31 3 1) v500_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v500_mg : Scalar.QComplex := ((-93085894291097722263574 : Int)/10^30,(-269232882057179281263 : Int)/10^30)
theorem v500_mg_checked : Scalar.distance (sourceCoefficient 5 31 3 2) v500_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v500_upper : Scalar.QComplex := ((999997940884658162050518187153 : Int)/10^30,(2029341381759093772610041504 : Int)/10^30)
theorem v500_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 31 5) 1) 14) v500_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material500 : Material (5 : Basis) (31 : Basis) where
  plus := ![v500_pa,v500_pb,v500_pg]
  minus := ![(Primitive.Addresses.material500 1).one,v500_mb,v500_mg]
  upper := v500_upper
  lower := (Primitive.Addresses.material500 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v500_pa_checked.trans (by decide +kernel)
    · exact v500_pb_checked.trans (by decide +kernel)
    · exact v500_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 31 Primitive.Addresses.material500
    · exact v500_mb_checked.trans (by decide +kernel)
    · exact v500_mg_checked.trans (by decide +kernel)
  upper_error := v500_upper_checked
  lower_error := reuse_lower_error 5 31 Primitive.Addresses.material500

def v501_pa : Scalar.QComplex := ((999992966970047260909639277499 : Int)/10^30,(3750468029722139172075038712 : Int)/10^30)
theorem v501_pa_checked : Scalar.distance (sourceCoefficient 5 32 1 0) v501_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v501_pb : Scalar.QComplex := ((1618237551791423401768038 : Int)/10^30,(-431473127581396950601218757 : Int)/10^30)
theorem v501_pb_checked : Scalar.distance (sourceCoefficient 5 32 1 1) v501_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v501_pg : Scalar.QComplex := ((-93085628641672073145760 : Int)/10^30,(-349117129598408066133 : Int)/10^30)
theorem v501_pg_checked : Scalar.distance (sourceCoefficient 5 32 1 2) v501_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v501_mb : Scalar.QComplex := ((1245895072973165963145032 : Int)/10^30,(-431474363390356738162894056 : Int)/10^30)
theorem v501_mb_checked : Scalar.distance (sourceCoefficient 5 32 3 1) v501_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v501_mg : Scalar.QComplex := ((-93085895253997498057864 : Int)/10^30,(-268788294509466311303 : Int)/10^30)
theorem v501_mg_checked : Scalar.distance (sourceCoefficient 5 32 3 2) v501_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v501_upper : Scalar.QComplex := ((999997950565569883124427734227 : Int)/10^30,(2024565301503576544008795264 : Int)/10^30)
theorem v501_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 32 5) 1) 14) v501_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material501 : Material (5 : Basis) (32 : Basis) where
  plus := ![v501_pa,v501_pb,v501_pg]
  minus := ![(Primitive.Addresses.material501 1).one,v501_mb,v501_mg]
  upper := v501_upper
  lower := (Primitive.Addresses.material501 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v501_pa_checked.trans (by decide +kernel)
    · exact v501_pb_checked.trans (by decide +kernel)
    · exact v501_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 32 Primitive.Addresses.material501
    · exact v501_mb_checked.trans (by decide +kernel)
    · exact v501_mg_checked.trans (by decide +kernel)
  upper_error := v501_upper_checked
  lower_error := reuse_lower_error 5 32 Primitive.Addresses.material501

def v502_pa : Scalar.QComplex := ((999992991911451687056500376973 : Int)/10^30,(3743811958862355309497435762 : Int)/10^30)
theorem v502_pa_checked : Scalar.distance (sourceCoefficient 5 33 1 0) v502_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v502_pb : Scalar.QComplex := ((1615365600290395277147386 : Int)/10^30,(-431473134178484130799469539 : Int)/10^30)
theorem v502_pb_checked : Scalar.distance (sourceCoefficient 5 33 1 1) v502_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v502_pg : Scalar.QComplex := ((-93085630514148679975434 : Int)/10^30,(-348497539018724716362 : Int)/10^30)
theorem v502_pg_checked : Scalar.distance (sourceCoefficient 5 33 1 2) v502_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v502_mb : Scalar.QComplex := ((1243023116848507522290687 : Int)/10^30,(-431474367509076664470801104 : Int)/10^30)
theorem v502_mb_checked : Scalar.distance (sourceCoefficient 5 33 3 1) v502_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v502_mg : Scalar.QComplex := ((-93085896591794642736005 : Int)/10^30,(-268168702544621872558 : Int)/10^30)
theorem v502_mg_checked : Scalar.distance (sourceCoefficient 5 33 3 2) v502_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v502_upper : Scalar.QComplex := ((999997964019162692023779445115 : Int)/10^30,(2017909197510626977077278087 : Int)/10^30)
theorem v502_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 33 5) 1) 14) v502_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material502 : Material (5 : Basis) (33 : Basis) where
  plus := ![v502_pa,v502_pb,v502_pg]
  minus := ![(Primitive.Addresses.material502 1).one,v502_mb,v502_mg]
  upper := v502_upper
  lower := (Primitive.Addresses.material502 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v502_pa_checked.trans (by decide +kernel)
    · exact v502_pb_checked.trans (by decide +kernel)
    · exact v502_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 33 Primitive.Addresses.material502
    · exact v502_mb_checked.trans (by decide +kernel)
    · exact v502_mg_checked.trans (by decide +kernel)
  upper_error := v502_upper_checked
  lower_error := reuse_lower_error 5 33 Primitive.Addresses.material502

def v503_pa : Scalar.QComplex := ((999993052306844957846493761944 : Int)/10^30,(3727645106450469272312737024 : Int)/10^30)
theorem v503_pa_checked : Scalar.distance (sourceCoefficient 5 34 1 0) v503_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v503_pb : Scalar.QComplex := ((1608389951119729962036290 : Int)/10^30,(-431473150095933658593939213 : Int)/10^30)
theorem v503_pb_checked : Scalar.distance (sourceCoefficient 5 34 1 1) v503_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v503_pg : Scalar.QComplex := ((-93085635042149262967839 : Int)/10^30,(-346992622743971910522 : Int)/10^30)
theorem v503_pg_checked : Scalar.distance (sourceCoefficient 5 34 1 2) v503_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v503_mb : Scalar.QComplex := ((1236047456539153149162271 : Int)/10^30,(-431474377406849202763230916 : Int)/10^30)
theorem v503_mb_checked : Scalar.distance (sourceCoefficient 5 34 3 1) v503_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v503_mg : Scalar.QComplex := ((-93085899821118573548125 : Int)/10^30,(-266663782922757604333 : Int)/10^30)
theorem v503_mg_checked : Scalar.distance (sourceCoefficient 5 34 3 2) v503_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v503_upper : Scalar.QComplex := ((999997996511945393448738279917 : Int)/10^30,(2001742264940398757402787679 : Int)/10^30)
theorem v503_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 34 5) 1) 14) v503_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material503 : Material (5 : Basis) (34 : Basis) where
  plus := ![v503_pa,v503_pb,v503_pg]
  minus := ![(Primitive.Addresses.material503 1).one,v503_mb,v503_mg]
  upper := v503_upper
  lower := (Primitive.Addresses.material503 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v503_pa_checked.trans (by decide +kernel)
    · exact v503_pb_checked.trans (by decide +kernel)
    · exact v503_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 34 Primitive.Addresses.material503
    · exact v503_mb_checked.trans (by decide +kernel)
    · exact v503_mg_checked.trans (by decide +kernel)
  upper_error := v503_upper_checked
  lower_error := reuse_lower_error 5 34 Primitive.Addresses.material503

def v504_pa : Scalar.QComplex := ((999993242447517159702078157873 : Int)/10^30,(3676283354308402259587387929 : Int)/10^30)
theorem v504_pa_checked : Scalar.distance (sourceCoefficient 5 35 1 0) v504_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v504_pb : Scalar.QComplex := ((1586228460790378842454898 : Int)/10^30,(-431473199667633118673172790 : Int)/10^30)
theorem v504_pb_checked : Scalar.distance (sourceCoefficient 5 35 1 1) v504_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v504_pg : Scalar.QComplex := ((-93085649239173964269879 : Int)/10^30,(-342211535335376096277 : Int)/10^30)
theorem v504_pg_checked : Scalar.distance (sourceCoefficient 5 35 1 2) v504_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v504_mb : Scalar.QComplex := ((1213885931683393701757489 : Int)/10^30,(-431474407854162167275809596 : Int)/10^30)
theorem v504_mb_checked : Scalar.distance (sourceCoefficient 5 35 3 1) v504_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v504_mg : Scalar.QComplex := ((-93085909892274887214222 : Int)/10^30,(-261882685042986231831 : Int)/10^30)
theorem v504_mg_checked : Scalar.distance (sourceCoefficient 5 35 3 2) v504_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v504_upper : Scalar.QComplex := ((999998098006609707657204452130 : Int)/10^30,(1950380261130077391692437181 : Int)/10^30)
theorem v504_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 35 5) 1) 14) v504_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material504 : Material (5 : Basis) (35 : Basis) where
  plus := ![v504_pa,v504_pb,v504_pg]
  minus := ![(Primitive.Addresses.material504 1).one,v504_mb,v504_mg]
  upper := v504_upper
  lower := (Primitive.Addresses.material504 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v504_pa_checked.trans (by decide +kernel)
    · exact v504_pb_checked.trans (by decide +kernel)
    · exact v504_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 35 Primitive.Addresses.material504
    · exact v504_mb_checked.trans (by decide +kernel)
    · exact v504_mg_checked.trans (by decide +kernel)
  upper_error := v504_upper_checked
  lower_error := reuse_lower_error 5 35 Primitive.Addresses.material504

def v505_pa : Scalar.QComplex := ((999993301670505312953160341236 : Int)/10^30,(3660138538601520515523099051 : Int)/10^30)
theorem v505_pa_checked : Scalar.distance (sourceCoefficient 5 36 1 0) v505_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v505_pb : Scalar.QComplex := ((1579262320781887128628338 : Int)/10^30,(-431473214936260425428352497 : Int)/10^30)
theorem v505_pb_checked : Scalar.distance (sourceCoefficient 5 36 1 1) v505_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v505_pg : Scalar.QComplex := ((-93085653642618958152142 : Int)/10^30,(-340708670467199144399 : Int)/10^30)
theorem v505_pg_checked : Scalar.distance (sourceCoefficient 5 36 1 2) v505_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v505_mb : Scalar.QComplex := ((1206919781092576589135034 : Int)/10^30,(-431474417111318704794166965 : Int)/10^30)
theorem v505_mb_checked : Scalar.distance (sourceCoefficient 5 36 3 1) v505_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v505_mg : Scalar.QComplex := ((-93085912998813546776978 : Int)/10^30,(-260379816934419848772 : Int)/10^30)
theorem v505_mg_checked : Scalar.distance (sourceCoefficient 5 36 3 2) v505_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v505_upper : Scalar.QComplex := ((999998129365022391386102752533 : Int)/10^30,(1934235367255497254758406460 : Int)/10^30)
theorem v505_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 36 5) 1) 14) v505_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material505 : Material (5 : Basis) (36 : Basis) where
  plus := ![v505_pa,v505_pb,v505_pg]
  minus := ![(Primitive.Addresses.material505 1).one,v505_mb,v505_mg]
  upper := v505_upper
  lower := (Primitive.Addresses.material505 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v505_pa_checked.trans (by decide +kernel)
    · exact v505_pb_checked.trans (by decide +kernel)
    · exact v505_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 36 Primitive.Addresses.material505
    · exact v505_mb_checked.trans (by decide +kernel)
    · exact v505_mg_checked.trans (by decide +kernel)
  upper_error := v505_upper_checked
  lower_error := reuse_lower_error 5 36 Primitive.Addresses.material505

def v506_pa : Scalar.QComplex := ((999993326879944548723859176991 : Int)/10^30,(3653244527864412994966221192 : Int)/10^30)
theorem v506_pa_checked : Scalar.distance (sourceCoefficient 5 37 1 0) v506_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v506_pb : Scalar.QComplex := ((1576287703794812429989266 : Int)/10^30,(-431473221410440784332058411 : Int)/10^30)
theorem v506_pb_checked : Scalar.distance (sourceCoefficient 5 37 1 1) v506_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v506_pg : Scalar.QComplex := ((-93085655514312854899348 : Int)/10^30,(-340066930937792294344 : Int)/10^30)
theorem v506_pg_checked : Scalar.distance (sourceCoefficient 5 37 1 2) v506_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v506_mb : Scalar.QComplex := ((1203945159626161678021362 : Int)/10^30,(-431474421018536164995007429 : Int)/10^30)
theorem v506_mb_checked : Scalar.distance (sourceCoefficient 5 37 3 1) v506_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v506_mg : Scalar.QComplex := ((-93085914316714435604373 : Int)/10^30,(-259738076028774419532 : Int)/10^30)
theorem v506_mg_checked : Scalar.distance (sourceCoefficient 5 37 3 2) v506_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v506_upper : Scalar.QComplex := ((999998142675986968179347451159 : Int)/10^30,(1927341323277003761257044826 : Int)/10^30)
theorem v506_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 37 5) 1) 14) v506_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material506 : Material (5 : Basis) (37 : Basis) where
  plus := ![v506_pa,v506_pb,v506_pg]
  minus := ![(Primitive.Addresses.material506 1).one,v506_mb,v506_mg]
  upper := v506_upper
  lower := (Primitive.Addresses.material506 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v506_pa_checked.trans (by decide +kernel)
    · exact v506_pb_checked.trans (by decide +kernel)
    · exact v506_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 37 Primitive.Addresses.material506
    · exact v506_mb_checked.trans (by decide +kernel)
    · exact v506_mg_checked.trans (by decide +kernel)
  upper_error := v506_upper_checked
  lower_error := reuse_lower_error 5 37 Primitive.Addresses.material506

def v507_pa : Scalar.QComplex := ((999993411732786911723083908478 : Int)/10^30,(3629943666355124412292427390 : Int)/10^30)
theorem v507_pa_checked : Scalar.distance (sourceCoefficient 5 38 1 0) v507_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v507_pb : Scalar.QComplex := ((1566233884723400182574545 : Int)/10^30,(-431473243089944622198725497 : Int)/10^30)
theorem v507_pb_checked : Scalar.distance (sourceCoefficient 5 38 1 1) v507_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v507_pg : Scalar.QComplex := ((-93085661802190636941239 : Int)/10^30,(-337897934649221258139 : Int)/10^30)
theorem v507_pg_checked : Scalar.distance (sourceCoefficient 5 38 1 2) v507_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v507_mb : Scalar.QComplex := ((1193891325589810349651799 : Int)/10^30,(-431474434022038879164806843 : Int)/10^30)
theorem v507_mb_checked : Scalar.distance (sourceCoefficient 5 38 3 1) v507_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v507_mg : Scalar.QComplex := ((-93085918732843767311681 : Int)/10^30,(-257569075121664499190 : Int)/10^30)
theorem v507_mg_checked : Scalar.distance (sourceCoefficient 5 38 3 2) v507_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v507_upper : Scalar.QComplex := ((999998187313529825449023005032 : Int)/10^30,(1904040350023303156394796271 : Int)/10^30)
theorem v507_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 38 5) 1) 14) v507_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material507 : Material (5 : Basis) (38 : Basis) where
  plus := ![v507_pa,v507_pb,v507_pg]
  minus := ![(Primitive.Addresses.material507 1).one,v507_mb,v507_mg]
  upper := v507_upper
  lower := (Primitive.Addresses.material507 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v507_pa_checked.trans (by decide +kernel)
    · exact v507_pb_checked.trans (by decide +kernel)
    · exact v507_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 38 Primitive.Addresses.material507
    · exact v507_mb_checked.trans (by decide +kernel)
    · exact v507_mg_checked.trans (by decide +kernel)
  upper_error := v507_upper_checked
  lower_error := reuse_lower_error 5 38 Primitive.Addresses.material507

def v508_pa : Scalar.QComplex := ((999993460708805165239557506673 : Int)/10^30,(3616426361387742959548603353 : Int)/10^30)
theorem v508_pa_checked : Scalar.distance (sourceCoefficient 5 39 1 0) v508_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v508_pb : Scalar.QComplex := ((1560401459428518516269502 : Int)/10^30,(-431473255523505390957946469 : Int)/10^30)
theorem v508_pb_checked : Scalar.distance (sourceCoefficient 5 39 1 1) v508_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v508_pg : Scalar.QComplex := ((-93085665422891921315218 : Int)/10^30,(-336639655687402137335 : Int)/10^30)
theorem v508_pg_checked : Scalar.distance (sourceCoefficient 5 39 1 2) v508_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v508_mb : Scalar.QComplex := ((1188058891737004218985392 : Int)/10^30,(-431474441422474671542275663 : Int)/10^30)
theorem v508_mb_checked : Scalar.distance (sourceCoefficient 5 39 3 1) v508_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v508_mg : Scalar.QComplex := ((-93085921267705630263918 : Int)/10^30,(-256310793503858003978 : Int)/10^30)
theorem v508_mg_checked : Scalar.distance (sourceCoefficient 5 39 3 2) v508_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v508_upper : Scalar.QComplex := ((999998212959833041566512410823 : Int)/10^30,(1890522980660195162482674786 : Int)/10^30)
theorem v508_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 39 5) 1) 14) v508_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material508 : Material (5 : Basis) (39 : Basis) where
  plus := ![v508_pa,v508_pb,v508_pg]
  minus := ![(Primitive.Addresses.material508 1).one,v508_mb,v508_mg]
  upper := v508_upper
  lower := (Primitive.Addresses.material508 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v508_pa_checked.trans (by decide +kernel)
    · exact v508_pb_checked.trans (by decide +kernel)
    · exact v508_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 39 Primitive.Addresses.material508
    · exact v508_mb_checked.trans (by decide +kernel)
    · exact v508_mg_checked.trans (by decide +kernel)
  upper_error := v508_upper_checked
  lower_error := reuse_lower_error 5 39 Primitive.Addresses.material508

def v509_pa : Scalar.QComplex := ((999993542671612049661376119662 : Int)/10^30,(3593691010480835345692471959 : Int)/10^30)
theorem v509_pa_checked : Scalar.distance (sourceCoefficient 5 40 1 0) v509_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v509_pb : Scalar.QComplex := ((1550591646618403456766382 : Int)/10^30,(-431473276198967931628562057 : Int)/10^30)
theorem v509_pb_checked : Scalar.distance (sourceCoefficient 5 40 1 1) v509_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v509_pg : Scalar.QComplex := ((-93085671467952843185934 : Int)/10^30,(-334523300885761757163 : Int)/10^30)
theorem v509_pg_checked : Scalar.distance (sourceCoefficient 5 40 1 2) v509_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v509_mb : Scalar.QComplex := ((1178249064737537814948269 : Int)/10^30,(-431474453632502876231904214 : Int)/10^30)
theorem v509_mb_checked : Scalar.distance (sourceCoefficient 5 40 3 1) v509_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v509_mg : Scalar.QComplex := ((-93085925486445424548462 : Int)/10^30,(-254194434273617922512 : Int)/10^30)
theorem v509_mg_checked : Scalar.distance (sourceCoefficient 5 40 3 2) v509_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v509_upper : Scalar.QComplex := ((999998255683364721615598814432 : Int)/10^30,(1867787522154552967787451627 : Int)/10^30)
theorem v509_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 40 5) 1) 14) v509_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material509 : Material (5 : Basis) (40 : Basis) where
  plus := ![v509_pa,v509_pb,v509_pg]
  minus := ![(Primitive.Addresses.material509 1).one,v509_mb,v509_mg]
  upper := v509_upper
  lower := (Primitive.Addresses.material509 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v509_pa_checked.trans (by decide +kernel)
    · exact v509_pb_checked.trans (by decide +kernel)
    · exact v509_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 40 Primitive.Addresses.material509
    · exact v509_mb_checked.trans (by decide +kernel)
    · exact v509_mg_checked.trans (by decide +kernel)
  upper_error := v509_upper_checked
  lower_error := reuse_lower_error 5 40 Primitive.Addresses.material509

def v510_pa : Scalar.QComplex := ((999993594617719998208586930354 : Int)/10^30,(3579207109274542925886347054 : Int)/10^30)
theorem v510_pa_checked : Scalar.distance (sourceCoefficient 5 41 1 0) v510_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v510_pb : Scalar.QComplex := ((1544342156324128744825508 : Int)/10^30,(-431473289215516147219331263 : Int)/10^30)
theorem v510_pb_checked : Scalar.distance (sourceCoefficient 5 41 1 1) v510_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v510_pg : Scalar.QComplex := ((-93085675289778087430600 : Int)/10^30,(-333175044882324007256 : Int)/10^30)
theorem v510_pg_checked : Scalar.distance (sourceCoefficient 5 41 1 2) v510_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v510_mb : Scalar.QComplex := ((1171999565537539088896438 : Int)/10^30,(-431474461256017587802133723 : Int)/10^30)
theorem v510_mb_checked : Scalar.distance (sourceCoefficient 5 41 3 1) v510_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v510_mg : Scalar.QComplex := ((-93085928144785037982388 : Int)/10^30,(-252846175474134443865 : Int)/10^30)
theorem v510_mg_checked : Scalar.distance (sourceCoefficient 5 41 3 2) v510_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v510_upper : Scalar.QComplex := ((999998282631495789729592484352 : Int)/10^30,(1853303552866060191109931606 : Int)/10^30)
theorem v510_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 41 5) 1) 14) v510_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material510 : Material (5 : Basis) (41 : Basis) where
  plus := ![v510_pa,v510_pb,v510_pg]
  minus := ![(Primitive.Addresses.material510 1).one,v510_mb,v510_mg]
  upper := v510_upper
  lower := (Primitive.Addresses.material510 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v510_pa_checked.trans (by decide +kernel)
    · exact v510_pb_checked.trans (by decide +kernel)
    · exact v510_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 41 Primitive.Addresses.material510
    · exact v510_mb_checked.trans (by decide +kernel)
    · exact v510_mg_checked.trans (by decide +kernel)
  upper_error := v510_upper_checked
  lower_error := reuse_lower_error 5 41 Primitive.Addresses.material510

def v511_pa : Scalar.QComplex := ((999993636367669541132671386076 : Int)/10^30,(3567523533923959610222326071 : Int)/10^30)
theorem v511_pa_checked : Scalar.distance (sourceCoefficient 5 42 1 0) v511_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v511_pb : Scalar.QComplex := ((1539300946226170603405772 : Int)/10^30,(-431473299627492321541178346 : Int)/10^30)
theorem v511_pb_checked : Scalar.distance (sourceCoefficient 5 42 1 1) v511_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v511_pg : Scalar.QComplex := ((-93085678356087880656299 : Int)/10^30,(-332087461489126147366 : Int)/10^30)
theorem v511_pg_checked : Scalar.distance (sourceCoefficient 5 42 1 2) v511_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v511_mb : Scalar.QComplex := ((1166958348331587361189064 : Int)/10^30,(-431474467317652618405930423 : Int)/10^30)
theorem v511_mb_checked : Scalar.distance (sourceCoefficient 5 42 3 1) v511_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v511_mg : Scalar.QComplex := ((-93085930272558204088759 : Int)/10^30,(-251758589839806336191 : Int)/10^30)
theorem v511_mg_checked : Scalar.distance (sourceCoefficient 5 42 3 2) v511_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v511_upper : Scalar.QComplex := ((999998304216592021577443412037 : Int)/10^30,(1841619922860164525718820037 : Int)/10^30)
theorem v511_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 42 5) 1) 14) v511_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material511 : Material (5 : Basis) (42 : Basis) where
  plus := ![v511_pa,v511_pb,v511_pg]
  minus := ![(Primitive.Addresses.material511 1).one,v511_mb,v511_mg]
  upper := v511_upper
  lower := (Primitive.Addresses.material511 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v511_pa_checked.trans (by decide +kernel)
    · exact v511_pb_checked.trans (by decide +kernel)
    · exact v511_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 42 Primitive.Addresses.material511
    · exact v511_mb_checked.trans (by decide +kernel)
    · exact v511_mg_checked.trans (by decide +kernel)
  upper_error := v511_upper_checked
  lower_error := reuse_lower_error 5 42 Primitive.Addresses.material511

def v512_pa : Scalar.QComplex := ((999993691465264047828385756493 : Int)/10^30,(3552045843495523990919652125 : Int)/10^30)
theorem v512_pa_checked : Scalar.distance (sourceCoefficient 5 43 1 0) v512_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v512_pb : Scalar.QComplex := ((1532622657688773469600351 : Int)/10^30,(-431473313299716597845921265 : Int)/10^30)
theorem v512_pb_checked : Scalar.distance (sourceCoefficient 5 43 1 1) v512_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v512_pg : Scalar.QComplex := ((-93085682395320755216323 : Int)/10^30,(-330646697137417779313 : Int)/10^30)
theorem v512_pg_checked : Scalar.distance (sourceCoefficient 5 43 1 2) v512_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v512_mb : Scalar.QComplex := ((1160280050482308486392378 : Int)/10^30,(-431474475226809575093282177 : Int)/10^30)
theorem v512_mb_checked : Scalar.distance (sourceCoefficient 5 43 3 1) v512_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v512_mg : Scalar.QComplex := ((-93085933068474828751045 : Int)/10^30,(-250317822538884332014 : Int)/10^30)
theorem v512_mg_checked : Scalar.distance (sourceCoefficient 5 43 3 2) v512_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v512_upper : Scalar.QComplex := ((999998332601014912505723513074 : Int)/10^30,(1826142160390480958507473455 : Int)/10^30)
theorem v512_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 43 5) 1) 14) v512_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material512 : Material (5 : Basis) (43 : Basis) where
  plus := ![v512_pa,v512_pb,v512_pg]
  minus := ![(Primitive.Addresses.material512 1).one,v512_mb,v512_mg]
  upper := v512_upper
  lower := (Primitive.Addresses.material512 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v512_pa_checked.trans (by decide +kernel)
    · exact v512_pb_checked.trans (by decide +kernel)
    · exact v512_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 43 Primitive.Addresses.material512
    · exact v512_mb_checked.trans (by decide +kernel)
    · exact v512_mg_checked.trans (by decide +kernel)
  upper_error := v512_upper_checked
  lower_error := reuse_lower_error 5 43 Primitive.Addresses.material512

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
