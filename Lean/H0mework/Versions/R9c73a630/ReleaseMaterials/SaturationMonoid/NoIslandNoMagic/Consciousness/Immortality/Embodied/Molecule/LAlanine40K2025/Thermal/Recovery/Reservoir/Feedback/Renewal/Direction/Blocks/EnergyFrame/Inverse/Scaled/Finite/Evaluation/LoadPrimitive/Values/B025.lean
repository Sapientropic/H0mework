import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B016
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B017

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v401_pa : Scalar.QComplex := ((999992579681743401415210348979 : Int)/10^30,(3852347524831338521829332271 : Int)/10^30)
theorem v401_pa_checked : Scalar.distance (sourceCoefficient 4 24 1 0) v401_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v401_pb : Scalar.QComplex := ((1662196250230012811002673 : Int)/10^30,(-431472992893496557609027975 : Int)/10^30)
theorem v401_pb_checked : Scalar.distance (sourceCoefficient 4 24 1 1) v401_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v401_pg : Scalar.QComplex := ((-93085596087330424494064 : Int)/10^30,(-358600726615995628615 : Int)/10^30)
theorem v401_pg_checked : Scalar.distance (sourceCoefficient 4 24 1 2) v401_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v401_mb : Scalar.QComplex := ((1289853871273514853230431 : Int)/10^30,(-431474266636883421851153097 : Int)/10^30)
theorem v401_mb_checked : Scalar.distance (sourceCoefficient 4 24 3 1) v401_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v401_mg : Scalar.QComplex := ((-93085870883585071699404 : Int)/10^30,(-278271916088807932008 : Int)/10^30)
theorem v401_mg_checked : Scalar.distance (sourceCoefficient 4 24 3 2) v401_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v401_upper : Scalar.QComplex := ((999997739112608966944233464754 : Int)/10^30,(2126445313299713475801729008 : Int)/10^30)
theorem v401_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 24 5) 1) 14) v401_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material401 : Material (4 : Basis) (24 : Basis) where
  plus := ![v401_pa,v401_pb,v401_pg]
  minus := ![(Primitive.Addresses.material401 1).one,v401_mb,v401_mg]
  upper := v401_upper
  lower := (Primitive.Addresses.material401 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v401_pa_checked.trans (by decide +kernel)
    · exact v401_pb_checked.trans (by decide +kernel)
    · exact v401_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 24 Primitive.Addresses.material401
    · exact v401_mb_checked.trans (by decide +kernel)
    · exact v401_mg_checked.trans (by decide +kernel)
  upper_error := v401_upper_checked
  lower_error := reuse_lower_error 4 24 Primitive.Addresses.material401

def v402_pa : Scalar.QComplex := ((999992667961267315402059067646 : Int)/10^30,(3829363355255964515233907385 : Int)/10^30)
theorem v402_pa_checked : Scalar.distance (sourceCoefficient 4 25 1 0) v402_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v402_pb : Scalar.QComplex := ((1652279073693971185851804 : Int)/10^30,(-431473016748854295091375683 : Int)/10^30)
theorem v402_pb_checked : Scalar.distance (sourceCoefficient 4 25 1 1) v402_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v402_pg : Scalar.QComplex := ((-93085602769405121264042 : Int)/10^30,(-356461209734469570445 : Int)/10^30)
theorem v402_pg_checked : Scalar.distance (sourceCoefficient 4 25 1 2) v402_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v402_mb : Scalar.QComplex := ((1279936677843991967787362 : Int)/10^30,(-431474281934155579340291627 : Int)/10^30)
theorem v402_mb_checked : Scalar.distance (sourceCoefficient 4 25 3 1) v402_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v402_mg : Scalar.QComplex := ((-93085875719350571933881 : Int)/10^30,(-276132394237592275742 : Int)/10^30)
theorem v402_mg_checked : Scalar.distance (sourceCoefficient 4 25 3 2) v402_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v402_upper : Scalar.QComplex := ((999997787723409819430629655173 : Int)/10^30,(2103461025594110521817204747 : Int)/10^30)
theorem v402_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 25 5) 1) 14) v402_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material402 : Material (4 : Basis) (25 : Basis) where
  plus := ![v402_pa,v402_pb,v402_pg]
  minus := ![(Primitive.Addresses.material402 1).one,v402_mb,v402_mg]
  upper := v402_upper
  lower := (Primitive.Addresses.material402 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v402_pa_checked.trans (by decide +kernel)
    · exact v402_pb_checked.trans (by decide +kernel)
    · exact v402_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 25 Primitive.Addresses.material402
    · exact v402_mb_checked.trans (by decide +kernel)
    · exact v402_mg_checked.trans (by decide +kernel)
  upper_error := v402_upper_checked
  lower_error := reuse_lower_error 4 25 Primitive.Addresses.material402

def v403_pa : Scalar.QComplex := ((999992696056880609618258103502 : Int)/10^30,(3822019478128764350278931201 : Int)/10^30)
theorem v403_pa_checked : Scalar.distance (sourceCoefficient 4 26 1 0) v403_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v403_pb : Scalar.QComplex := ((1649110348196752245318901 : Int)/10^30,(-431473024307023972350339351 : Int)/10^30)
theorem v403_pb_checked : Scalar.distance (sourceCoefficient 4 26 1 1) v403_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v403_pg : Scalar.QComplex := ((-93085604892360104880114 : Int)/10^30,(-355777593611305412238 : Int)/10^30)
theorem v403_pg_checked : Scalar.distance (sourceCoefficient 4 26 1 2) v403_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v403_mb : Scalar.QComplex := ((1276767947004274323629707 : Int)/10^30,(-431474286757855052345911728 : Int)/10^30)
theorem v403_mb_checked : Scalar.distance (sourceCoefficient 4 26 3 1) v403_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v403_mg : Scalar.QComplex := ((-93085877252374839713369 : Int)/10^30,(-275448776536955106472 : Int)/10^30)
theorem v403_mg_checked : Scalar.distance (sourceCoefficient 4 26 3 2) v403_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v403_upper : Scalar.QComplex := ((999997803144115578312350881451 : Int)/10^30,(2096117110914272933730730372 : Int)/10^30)
theorem v403_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 26 5) 1) 14) v403_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material403 : Material (4 : Basis) (26 : Basis) where
  plus := ![v403_pa,v403_pb,v403_pg]
  minus := ![(Primitive.Addresses.material403 1).one,v403_mb,v403_mg]
  upper := v403_upper
  lower := (Primitive.Addresses.material403 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v403_pa_checked.trans (by decide +kernel)
    · exact v403_pb_checked.trans (by decide +kernel)
    · exact v403_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 26 Primitive.Addresses.material403
    · exact v403_mb_checked.trans (by decide +kernel)
    · exact v403_mg_checked.trans (by decide +kernel)
  upper_error := v403_upper_checked
  lower_error := reuse_lower_error 4 26 Primitive.Addresses.material403

def v404_pa : Scalar.QComplex := ((999992715327134145759200458175 : Int)/10^30,(3816974281449865766968669398 : Int)/10^30)
theorem v404_pa_checked : Scalar.distance (sourceCoefficient 4 27 1 0) v404_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v404_pb : Scalar.QComplex := ((1646933454041430070569044 : Int)/10^30,(-431473029481458170199051680 : Int)/10^30)
theorem v404_pb_checked : Scalar.distance (sourceCoefficient 4 27 1 1) v404_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v404_pg : Scalar.QComplex := ((-93085606347422485062053 : Int)/10^30,(-355307953703487369805 : Int)/10^30)
theorem v404_pg_checked : Scalar.distance (sourceCoefficient 4 27 1 2) v404_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v404_mb : Scalar.QComplex := ((1274591049194205667005739 : Int)/10^30,(-431474290053725711146455547 : Int)/10^30)
theorem v404_mb_checked : Scalar.distance (sourceCoefficient 4 27 3 1) v404_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v404_mg : Scalar.QComplex := ((-93085878302158589458370 : Int)/10^30,(-274979135548352164804 : Int)/10^30)
theorem v404_mg_checked : Scalar.distance (sourceCoefficient 4 27 3 2) v404_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v404_upper : Scalar.QComplex := ((999997813706788642562718875557 : Int)/10^30,(2091071888490892733572052891 : Int)/10^30)
theorem v404_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 27 5) 1) 14) v404_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material404 : Material (4 : Basis) (27 : Basis) where
  plus := ![v404_pa,v404_pb,v404_pg]
  minus := ![(Primitive.Addresses.material404 1).one,v404_mb,v404_mg]
  upper := v404_upper
  lower := (Primitive.Addresses.material404 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v404_pa_checked.trans (by decide +kernel)
    · exact v404_pb_checked.trans (by decide +kernel)
    · exact v404_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 27 Primitive.Addresses.material404
    · exact v404_mb_checked.trans (by decide +kernel)
    · exact v404_mg_checked.trans (by decide +kernel)
  upper_error := v404_upper_checked
  lower_error := reuse_lower_error 4 27 Primitive.Addresses.material404

def v405_pa : Scalar.QComplex := ((999992741246425971716549004998 : Int)/10^30,(3810177746320126524290088241 : Int)/10^30)
theorem v405_pa_checked : Scalar.distance (sourceCoefficient 4 28 1 0) v405_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v405_pb : Scalar.QComplex := ((1644000894936098358426346 : Int)/10^30,(-431473036428941594014805519 : Int)/10^30)
theorem v405_pb_checked : Scalar.distance (sourceCoefficient 4 28 1 1) v405_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v405_pg : Scalar.QComplex := ((-93085608303210140152307 : Int)/10^30,(-354675287760075916578 : Int)/10^30)
theorem v405_pg_checked : Scalar.distance (sourceCoefficient 4 28 1 2) v405_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v405_mb : Scalar.QComplex := ((1271658485185434442635005 : Int)/10^30,(-431474294470540117754502122 : Int)/10^30)
theorem v405_mb_checked : Scalar.distance (sourceCoefficient 4 28 3 1) v405_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v405_mg : Scalar.QComplex := ((-93085879711983301371748 : Int)/10^30,(-274346468152754495634 : Int)/10^30)
theorem v405_mg_checked : Scalar.distance (sourceCoefficient 4 28 3 2) v405_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v405_upper : Scalar.QComplex := ((999997827895838807700189597497 : Int)/10^30,(2084275318749447877724898527 : Int)/10^30)
theorem v405_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 28 5) 1) 14) v405_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material405 : Material (4 : Basis) (28 : Basis) where
  plus := ![v405_pa,v405_pb,v405_pg]
  minus := ![(Primitive.Addresses.material405 1).one,v405_mb,v405_mg]
  upper := v405_upper
  lower := (Primitive.Addresses.material405 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v405_pa_checked.trans (by decide +kernel)
    · exact v405_pb_checked.trans (by decide +kernel)
    · exact v405_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 28 Primitive.Addresses.material405
    · exact v405_mb_checked.trans (by decide +kernel)
    · exact v405_mg_checked.trans (by decide +kernel)
  upper_error := v405_upper_checked
  lower_error := reuse_lower_error 4 28 Primitive.Addresses.material405

def v406_pa : Scalar.QComplex := ((999992793600141642751246677935 : Int)/10^30,(3796412488720842222499509131 : Int)/10^30)
theorem v406_pa_checked : Scalar.distance (sourceCoefficient 4 29 1 0) v406_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v406_pb : Scalar.QComplex := ((1638061481681308267855621 : Int)/10^30,(-431473050418502023060034923 : Int)/10^30)
theorem v406_pb_checked : Scalar.distance (sourceCoefficient 4 29 1 1) v406_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v406_pg : Scalar.QComplex := ((-93085612248965090850695 : Int)/10^30,(-353393927560146389349 : Int)/10^30)
theorem v406_pg_checked : Scalar.distance (sourceCoefficient 4 29 1 2) v406_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v406_mb : Scalar.QComplex := ((1265719062069798767564537 : Int)/10^30,(-431474303334649200206063974 : Int)/10^30)
theorem v406_mb_checked : Scalar.distance (sourceCoefficient 4 29 3 1) v406_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v406_mg : Scalar.QComplex := ((-93085882551980640667153 : Int)/10^30,(-273065105024925119646 : Int)/10^30)
theorem v406_mg_checked : Scalar.distance (sourceCoefficient 4 29 3 2) v406_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v406_upper : Scalar.QComplex := ((999997856491890662075106501652 : Int)/10^30,(2070509991294134033102765642 : Int)/10^30)
theorem v406_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 29 5) 1) 14) v406_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material406 : Material (4 : Basis) (29 : Basis) where
  plus := ![v406_pa,v406_pb,v406_pg]
  minus := ![(Primitive.Addresses.material406 1).one,v406_mb,v406_mg]
  upper := v406_upper
  lower := (Primitive.Addresses.material406 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v406_pa_checked.trans (by decide +kernel)
    · exact v406_pb_checked.trans (by decide +kernel)
    · exact v406_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 29 Primitive.Addresses.material406
    · exact v406_mb_checked.trans (by decide +kernel)
    · exact v406_mg_checked.trans (by decide +kernel)
  upper_error := v406_upper_checked
  lower_error := reuse_lower_error 4 29 Primitive.Addresses.material406

def v407_pa : Scalar.QComplex := ((999992813389754261816453294006 : Int)/10^30,(3791196228647304262927495364 : Int)/10^30)
theorem v407_pa_checked : Scalar.distance (sourceCoefficient 4 30 1 0) v407_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v407_pb : Scalar.QComplex := ((1635810777434197039354661 : Int)/10^30,(-431473055691278635003823980 : Int)/10^30)
theorem v407_pb_checked : Scalar.distance (sourceCoefficient 4 30 1 1) v407_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v407_pg : Scalar.QComplex := ((-93085613738808237258334 : Int)/10^30,(-352908363962753742325 : Int)/10^30)
theorem v407_pg_checked : Scalar.distance (sourceCoefficient 4 30 1 2) v407_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v407_mb : Scalar.QComplex := ((1263468354110558853464229 : Int)/10^30,(-431474306665167451553486884 : Int)/10^30)
theorem v407_mb_checked : Scalar.distance (sourceCoefficient 4 30 3 1) v407_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v407_mg : Scalar.QComplex := ((-93085883622803716760857 : Int)/10^30,(-272579540322662455979 : Int)/10^30)
theorem v407_mg_checked : Scalar.distance (sourceCoefficient 4 30 3 2) v407_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v407_upper : Scalar.QComplex := ((999997867278682135327765379547 : Int)/10^30,(2065293704834526627240463560 : Int)/10^30)
theorem v407_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 30 5) 1) 14) v407_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material407 : Material (4 : Basis) (30 : Basis) where
  plus := ![v407_pa,v407_pb,v407_pg]
  minus := ![(Primitive.Addresses.material407 1).one,v407_mb,v407_mg]
  upper := v407_upper
  lower := (Primitive.Addresses.material407 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v407_pa_checked.trans (by decide +kernel)
    · exact v407_pb_checked.trans (by decide +kernel)
    · exact v407_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 30 Primitive.Addresses.material407
    · exact v407_mb_checked.trans (by decide +kernel)
    · exact v407_mg_checked.trans (by decide +kernel)
  upper_error := v407_upper_checked
  lower_error := reuse_lower_error 4 30 Primitive.Addresses.material407

def v408_pa : Scalar.QComplex := ((999992855391790021104466429604 : Int)/10^30,(3780101238661646872652515473 : Int)/10^30)
theorem v408_pa_checked : Scalar.distance (sourceCoefficient 4 31 1 0) v408_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v408_pb : Scalar.QComplex := ((1631023527489622190962002 : Int)/10^30,(-431473066854421165783198143 : Int)/10^30)
theorem v408_pb_checked : Scalar.distance (sourceCoefficient 4 31 1 1) v408_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v408_pg : Scalar.QComplex := ((-93085616897878869323146 : Int)/10^30,(-351875569750339970092 : Int)/10^30)
theorem v408_pg_checked : Scalar.distance (sourceCoefficient 4 31 1 2) v408_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v408_mb : Scalar.QComplex := ((1258681096315206712780920 : Int)/10^30,(-431474313697124733350315972 : Int)/10^30)
theorem v408_mb_checked : Scalar.distance (sourceCoefficient 4 31 3 1) v408_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v408_mg : Scalar.QComplex := ((-93085885890618282570808 : Int)/10^30,(-271546743768669493843 : Int)/10^30)
theorem v408_mg_checked : Scalar.distance (sourceCoefficient 4 31 3 2) v408_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v408_upper : Scalar.QComplex := ((999997890131709151901686012238 : Int)/10^30,(2054198658881850185913782267 : Int)/10^30)
theorem v408_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 31 5) 1) 14) v408_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material408 : Material (4 : Basis) (31 : Basis) where
  plus := ![v408_pa,v408_pb,v408_pg]
  minus := ![(Primitive.Addresses.material408 1).one,v408_mb,v408_mg]
  upper := v408_upper
  lower := (Primitive.Addresses.material408 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v408_pa_checked.trans (by decide +kernel)
    · exact v408_pb_checked.trans (by decide +kernel)
    · exact v408_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 31 Primitive.Addresses.material408
    · exact v408_mb_checked.trans (by decide +kernel)
    · exact v408_mg_checked.trans (by decide +kernel)
  upper_error := v408_upper_checked
  lower_error := reuse_lower_error 4 31 Primitive.Addresses.material408

def v409_pa : Scalar.QComplex := ((999992873434488562246371698929 : Int)/10^30,(3775325182674933293480686857 : Int)/10^30)
theorem v409_pa_checked : Scalar.distance (sourceCoefficient 4 32 1 0) v409_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v409_pb : Scalar.QComplex := ((1628962761910923392997928 : Int)/10^30,(-431473071638010068753222244 : Int)/10^30)
theorem v409_pb_checked : Scalar.distance (sourceCoefficient 4 32 1 1) v409_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v409_pg : Scalar.QComplex := ((-93085618253646657103906 : Int)/10^30,(-351430983233782435331 : Int)/10^30)
theorem v409_pg_checked : Scalar.distance (sourceCoefficient 4 32 1 2) v409_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v409_mb : Scalar.QComplex := ((1256620327375803342989392 : Int)/10^30,(-431474316702363974190775928 : Int)/10^30)
theorem v409_mb_checked : Scalar.distance (sourceCoefficient 4 32 3 1) v409_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v409_mg : Scalar.QComplex := ((-93085886862727425181507 : Int)/10^30,(-271102156247685298463 : Int)/10^30)
theorem v409_mg_checked : Scalar.distance (sourceCoefficient 4 32 3 2) v409_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v409_upper : Scalar.QComplex := ((999997899931341467910434652771 : Int)/10^30,(2049422578868450102819656244 : Int)/10^30)
theorem v409_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 32 5) 1) 14) v409_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material409 : Material (4 : Basis) (32 : Basis) where
  plus := ![v409_pa,v409_pb,v409_pg]
  minus := ![(Primitive.Addresses.material409 1).one,v409_mb,v409_mg]
  upper := v409_upper
  lower := (Primitive.Addresses.material409 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v409_pa_checked.trans (by decide +kernel)
    · exact v409_pb_checked.trans (by decide +kernel)
    · exact v409_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 32 Primitive.Addresses.material409
    · exact v409_mb_checked.trans (by decide +kernel)
    · exact v409_mg_checked.trans (by decide +kernel)
  upper_error := v409_upper_checked
  lower_error := reuse_lower_error 4 32 Primitive.Addresses.material409

def v410_pa : Scalar.QComplex := ((999992898541345123456181485835 : Int)/10^30,(3768669112437182473963253300 : Int)/10^30)
theorem v410_pa_checked : Scalar.distance (sourceCoefficient 4 33 1 0) v410_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v410_pb : Scalar.QComplex := ((1626090810588823776979062 : Int)/10^30,(-431473078282689742794697402 : Int)/10^30)
theorem v410_pb_checked : Scalar.distance (sourceCoefficient 4 33 1 1) v410_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v410_pg : Scalar.QComplex := ((-93085620138957706412237 : Int)/10^30,(-350811392702351393140 : Int)/10^30)
theorem v410_pg_checked : Scalar.distance (sourceCoefficient 4 33 1 2) v410_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v410_mb : Scalar.QComplex := ((1253748371389003165413222 : Int)/10^30,(-431474320868676531028291092 : Int)/10^30)
theorem v410_mb_checked : Scalar.distance (sourceCoefficient 4 33 3 1) v410_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v410_mg : Scalar.QComplex := ((-93085888213359049199024 : Int)/10^30,(-270482564320017603515 : Int)/10^30)
theorem v410_mg_checked : Scalar.distance (sourceCoefficient 4 33 3 2) v410_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v410_upper : Scalar.QComplex := ((999997913550387239023817172869 : Int)/10^30,(2042766475211977277084954086 : Int)/10^30)
theorem v410_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 33 5) 1) 14) v410_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material410 : Material (4 : Basis) (33 : Basis) where
  plus := ![v410_pa,v410_pb,v410_pg]
  minus := ![(Primitive.Addresses.material410 1).one,v410_mb,v410_mg]
  upper := v410_upper
  lower := (Primitive.Addresses.material410 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v410_pa_checked.trans (by decide +kernel)
    · exact v410_pb_checked.trans (by decide +kernel)
    · exact v410_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 33 Primitive.Addresses.material410
    · exact v410_mb_checked.trans (by decide +kernel)
    · exact v410_mg_checked.trans (by decide +kernel)
  upper_error := v410_upper_checked
  lower_error := reuse_lower_error 4 33 Primitive.Addresses.material410

def v411_pa : Scalar.QComplex := ((999992959338603143814114850104 : Int)/10^30,(3752502261531559235763855735 : Int)/10^30)
theorem v411_pa_checked : Scalar.distance (sourceCoefficient 4 34 1 0) v411_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v411_pb : Scalar.QComplex := ((1619115161851436655856639 : Int)/10^30,(-431473094315736119319023777 : Int)/10^30)
theorem v411_pb_checked : Scalar.distance (sourceCoefficient 4 34 1 1) v411_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v411_pg : Scalar.QComplex := ((-93085624698131715965192 : Int)/10^30,(-349306476544442308466 : Int)/10^30)
theorem v411_pg_checked : Scalar.distance (sourceCoefficient 4 34 1 2) v411_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v411_mb : Scalar.QComplex := ((1246772711413171950779139 : Int)/10^30,(-431474330882046248908155074 : Int)/10^30)
theorem v411_mb_checked : Scalar.distance (sourceCoefficient 4 34 3 1) v411_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v411_mg : Scalar.QComplex := ((-93085891473856495795271 : Int)/10^30,(-268977644788095749827 : Int)/10^30)
theorem v411_mg_checked : Scalar.distance (sourceCoefficient 4 34 3 2) v411_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v411_upper : Scalar.QComplex := ((999997946445036691159321810007 : Int)/10^30,(2026599543454427512125294661 : Int)/10^30)
theorem v411_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 34 5) 1) 14) v411_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material411 : Material (4 : Basis) (34 : Basis) where
  plus := ![v411_pa,v411_pb,v411_pg]
  minus := ![(Primitive.Addresses.material411 1).one,v411_mb,v411_mg]
  upper := v411_upper
  lower := (Primitive.Addresses.material411 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v411_pa_checked.trans (by decide +kernel)
    · exact v411_pb_checked.trans (by decide +kernel)
    · exact v411_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 34 Primitive.Addresses.material411
    · exact v411_mb_checked.trans (by decide +kernel)
    · exact v411_mg_checked.trans (by decide +kernel)
  upper_error := v411_upper_checked
  lower_error := reuse_lower_error 4 34 Primitive.Addresses.material411

def v412_pa : Scalar.QComplex := ((999993150755991254539451093757 : Int)/10^30,(3701140514131749330040251921 : Int)/10^30)
theorem v412_pa_checked : Scalar.distance (sourceCoefficient 4 35 1 0) v412_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v412_pb : Scalar.QComplex := ((1596953672886201104465334 : Int)/10^30,(-431473144254684340500690406 : Int)/10^30)
theorem v412_pb_checked : Scalar.distance (sourceCoefficient 4 35 1 1) v412_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v412_pg : Scalar.QComplex := ((-93085638994193740043312 : Int)/10^30,(-344525389503712551613 : Int)/10^30)
theorem v412_pg_checked : Scalar.distance (sourceCoefficient 4 35 1 2) v412_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v412_mb : Scalar.QComplex := ((1224611187604608423080672 : Int)/10^30,(-431474361696609014949966813 : Int)/10^30)
theorem v412_mb_checked : Scalar.distance (sourceCoefficient 4 35 3 1) v412_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v412_mg : Scalar.QComplex := ((-93085901644050412813165 : Int)/10^30,(-264196547190725548662 : Int)/10^30)
theorem v412_mg_checked : Scalar.distance (sourceCoefficient 4 35 3 2) v412_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v412_upper : Scalar.QComplex := ((999998049216423197424719635089 : Int)/10^30,(1975237542182860354435096421 : Int)/10^30)
theorem v412_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 35 5) 1) 14) v412_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material412 : Material (4 : Basis) (35 : Basis) where
  plus := ![v412_pa,v412_pb,v412_pg]
  minus := ![(Primitive.Addresses.material412 1).one,v412_mb,v412_mg]
  upper := v412_upper
  lower := (Primitive.Addresses.material412 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v412_pa_checked.trans (by decide +kernel)
    · exact v412_pb_checked.trans (by decide +kernel)
    · exact v412_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 35 Primitive.Addresses.material412
    · exact v412_mb_checked.trans (by decide +kernel)
    · exact v412_mg_checked.trans (by decide +kernel)
  upper_error := v412_upper_checked
  lower_error := reuse_lower_error 4 35 Primitive.Addresses.material412

def v413_pa : Scalar.QComplex := ((999993210380296384095770910539 : Int)/10^30,(3684995699901980717216322118 : Int)/10^30)
theorem v413_pa_checked : Scalar.distance (sourceCoefficient 4 36 1 0) v413_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v413_pb : Scalar.QComplex := ((1589987533302602624513925 : Int)/10^30,(-431473159638750921517394486 : Int)/10^30)
theorem v413_pb_checked : Scalar.distance (sourceCoefficient 4 36 1 1) v413_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v413_pg : Scalar.QComplex := ((-93085643428769667541970 : Int)/10^30,(-343022524750118120652 : Int)/10^30)
theorem v413_pg_checked : Scalar.distance (sourceCoefficient 4 36 1 2) v413_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v413_mb : Scalar.QComplex := ((1217645037339065491630413 : Int)/10^30,(-431474371069205150410255266 : Int)/10^30)
theorem v413_mb_checked : Scalar.distance (sourceCoefficient 4 36 3 1) v413_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v413_mg : Scalar.QComplex := ((-93085904781720093280402 : Int)/10^30,(-262693679169877050231 : Int)/10^30)
theorem v413_mg_checked : Scalar.distance (sourceCoefficient 4 36 3 2) v413_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v413_upper : Scalar.QComplex := ((999998080976154809107623230206 : Int)/10^30,(1959092649092754454843782571 : Int)/10^30)
theorem v413_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 36 5) 1) 14) v413_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material413 : Material (4 : Basis) (36 : Basis) where
  plus := ![v413_pa,v413_pb,v413_pg]
  minus := ![(Primitive.Addresses.material413 1).one,v413_mb,v413_mg]
  upper := v413_upper
  lower := (Primitive.Addresses.material413 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v413_pa_checked.trans (by decide +kernel)
    · exact v413_pb_checked.trans (by decide +kernel)
    · exact v413_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 36 Primitive.Addresses.material413
    · exact v413_mb_checked.trans (by decide +kernel)
    · exact v413_mg_checked.trans (by decide +kernel)
  upper_error := v413_upper_checked
  lower_error := reuse_lower_error 4 36 Primitive.Addresses.material413

def v414_pa : Scalar.QComplex := ((999993235761102304643716699805 : Int)/10^30,(3678101689793642379103058377 : Int)/10^30)
theorem v414_pa_checked : Scalar.distance (sourceCoefficient 4 37 1 0) v414_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v414_pb : Scalar.QComplex := ((1587012916496394078169559 : Int)/10^30,(-431473166162225097250772205 : Int)/10^30)
theorem v414_pb_checked : Scalar.distance (sourceCoefficient 4 37 1 1) v414_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v414_pg : Scalar.QComplex := ((-93085645313756809205416 : Int)/10^30,(-342380785269486111220 : Int)/10^30)
theorem v414_pg_checked : Scalar.distance (sourceCoefficient 4 37 1 2) v414_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v414_mb : Scalar.QComplex := ((1214670416010978321653801 : Int)/10^30,(-431474375025716565165770212 : Int)/10^30)
theorem v414_mb_checked : Scalar.distance (sourceCoefficient 4 37 3 1) v414_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v414_mg : Scalar.QComplex := ((-93085906112914264164846 : Int)/10^30,(-262051938301534971795 : Int)/10^30)
theorem v414_mg_checked : Scalar.distance (sourceCoefficient 4 37 3 2) v414_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v414_upper : Scalar.QComplex := ((999998094458486900646135454523 : Int)/10^30,(1952198605447265855646872222 : Int)/10^30)
theorem v414_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 37 5) 1) 14) v414_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material414 : Material (4 : Basis) (37 : Basis) where
  plus := ![v414_pa,v414_pb,v414_pg]
  minus := ![(Primitive.Addresses.material414 1).one,v414_mb,v414_mg]
  upper := v414_upper
  lower := (Primitive.Addresses.material414 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v414_pa_checked.trans (by decide +kernel)
    · exact v414_pb_checked.trans (by decide +kernel)
    · exact v414_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 37 Primitive.Addresses.material414
    · exact v414_mb_checked.trans (by decide +kernel)
    · exact v414_mg_checked.trans (by decide +kernel)
  upper_error := v414_upper_checked
  lower_error := reuse_lower_error 4 37 Primitive.Addresses.material414

def v415_pa : Scalar.QComplex := ((999993321193141820405880534299 : Int)/10^30,(3654800830400767457414327692 : Int)/10^30)
theorem v415_pa_checked : Scalar.distance (sourceCoefficient 4 38 1 0) v415_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v415_pb : Scalar.QComplex := ((1576959098033770558098570 : Int)/10^30,(-431473188008335635883150287 : Int)/10^30)
theorem v415_pb_checked : Scalar.distance (sourceCoefficient 4 38 1 1) v415_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v415_pg : Scalar.QComplex := ((-93085651646564033362818 : Int)/10^30,(-340211789145089371488 : Int)/10^30)
theorem v415_pg_checked : Scalar.distance (sourceCoefficient 4 38 1 2) v415_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v415_mb : Scalar.QComplex := ((1204616582439641414874548 : Int)/10^30,(-431474388195826443423244495 : Int)/10^30)
theorem v415_mb_checked : Scalar.distance (sourceCoefficient 4 38 3 1) v415_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v415_mg : Scalar.QComplex := ((-93085910573973162933403 : Int)/10^30,(-259882937519827201797 : Int)/10^30)
theorem v415_mg_checked : Scalar.distance (sourceCoefficient 4 38 3 2) v415_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v415_upper : Scalar.QComplex := ((999998139675229700770607660640 : Int)/10^30,(1928897633310334018306561942 : Int)/10^30)
theorem v415_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 38 5) 1) 14) v415_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material415 : Material (4 : Basis) (38 : Basis) where
  plus := ![v415_pa,v415_pb,v415_pg]
  minus := ![(Primitive.Addresses.material415 1).one,v415_mb,v415_mg]
  upper := v415_upper
  lower := (Primitive.Addresses.material415 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v415_pa_checked.trans (by decide +kernel)
    · exact v415_pb_checked.trans (by decide +kernel)
    · exact v415_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 38 Primitive.Addresses.material415
    · exact v415_mb_checked.trans (by decide +kernel)
    · exact v415_mg_checked.trans (by decide +kernel)
  upper_error := v415_upper_checked
  lower_error := reuse_lower_error 4 38 Primitive.Addresses.material415

def v416_pa : Scalar.QComplex := ((999993370505164154664434190010 : Int)/10^30,(3641283526654975082434466187 : Int)/10^30)
theorem v416_pa_checked : Scalar.distance (sourceCoefficient 4 39 1 0) v416_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v416_pb : Scalar.QComplex := ((1571126673090280333568514 : Int)/10^30,(-431473200538548348020428224 : Int)/10^30)
theorem v416_pb_checked : Scalar.distance (sourceCoefficient 4 39 1 1) v416_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v416_pg : Scalar.QComplex := ((-93085655293329803162819 : Int)/10^30,(-338953510278031274548 : Int)/10^30)
theorem v416_pg_checked : Scalar.distance (sourceCoefficient 4 39 1 2) v416_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v416_mb : Scalar.QComplex := ((1198784148854820321050708 : Int)/10^30,(-431474395692914446425822718 : Int)/10^30)
theorem v416_mb_checked : Scalar.distance (sourceCoefficient 4 39 3 1) v416_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v416_mg : Scalar.QComplex := ((-93085913134899583381160 : Int)/10^30,(-258624655974289218144 : Int)/10^30)
theorem v416_mg_checked : Scalar.distance (sourceCoefficient 4 39 3 2) v416_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v416_upper : Scalar.QComplex := ((999998165657538605543495195702 : Int)/10^30,(1915380264588900721436231612 : Int)/10^30)
theorem v416_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 39 5) 1) 14) v416_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material416 : Material (4 : Basis) (39 : Basis) where
  plus := ![v416_pa,v416_pb,v416_pg]
  minus := ![(Primitive.Addresses.material416 1).one,v416_mb,v416_mg]
  upper := v416_upper
  lower := (Primitive.Addresses.material416 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v416_pa_checked.trans (by decide +kernel)
    · exact v416_pb_checked.trans (by decide +kernel)
    · exact v416_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 39 Primitive.Addresses.material416
    · exact v416_mb_checked.trans (by decide +kernel)
    · exact v416_mg_checked.trans (by decide +kernel)
  upper_error := v416_upper_checked
  lower_error := reuse_lower_error 4 39 Primitive.Addresses.material416

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
