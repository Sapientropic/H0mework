import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B133
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B134

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3201_pa : Scalar.QComplex := ((999998526027975515932296408929 : Int)/10^30,(-1716957156243162185656172658 : Int)/10^30)
theorem v3201_pa_checked : Scalar.distance (sourceCoefficient 41 86 1 0) v3201_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3201_pb : Scalar.QComplex := ((-740828342703527213942934 : Int)/10^30,(-431476841486402396992813792 : Int)/10^30)
theorem v3201_pb_checked : Scalar.distance (sourceCoefficient 41 86 1 1) v3201_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3201_pg : Scalar.QComplex := ((-93086287994794822915085 : Int)/10^30,(159825403898949076117 : Int)/10^30)
theorem v3201_pg_checked : Scalar.distance (sourceCoefficient 41 86 1 2) v3201_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3201_mb : Scalar.QComplex := ((-1113173148066489122639600 : Int)/10^30,(-431476041526360762607388345 : Int)/10^30)
theorem v3201_mb_checked : Scalar.distance (sourceCoefficient 41 86 3 1) v3201_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3201_mg : Scalar.QComplex := ((-93086115412390253113473 : Int)/10^30,(240154618477374557817 : Int)/10^30)
theorem v3201_mg_checked : Scalar.distance (sourceCoefficient 41 86 3 2) v3201_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3201_upper : Scalar.QComplex := ((999994073335348536589692307746 : Int)/10^30,(-3442861335803829568673521134 : Int)/10^30)
theorem v3201_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 86 5) 1) 14) v3201_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3201 : Material (41 : Basis) (86 : Basis) where
  plus := ![v3201_pa,v3201_pb,v3201_pg]
  minus := ![(Primitive.Addresses.material3201 1).one,v3201_mb,v3201_mg]
  upper := v3201_upper
  lower := (Primitive.Addresses.material3201 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3201_pa_checked.trans (by decide +kernel)
    · exact v3201_pb_checked.trans (by decide +kernel)
    · exact v3201_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 86 Primitive.Addresses.material3201
    · exact v3201_mb_checked.trans (by decide +kernel)
    · exact v3201_mg_checked.trans (by decide +kernel)
  upper_error := v3201_upper_checked
  lower_error := reuse_lower_error 41 86 Primitive.Addresses.material3201

def v3202_pa : Scalar.QComplex := ((999998524369346742309139338615 : Int)/10^30,(-1717922911259279086631865246 : Int)/10^30)
theorem v3202_pa_checked : Scalar.distance (sourceCoefficient 41 87 1 0) v3202_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3202_pb : Scalar.QComplex := ((-741245044055973571649255 : Int)/10^30,(-431476840662608792786120103 : Int)/10^30)
theorem v3202_pb_checked : Scalar.distance (sourceCoefficient 41 87 1 1) v3202_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3202_pg : Scalar.QComplex := ((-93086287828734797581785 : Int)/10^30,(159915302560981664558 : Int)/10^30)
theorem v3202_pg_checked : Scalar.distance (sourceCoefficient 41 87 1 2) v3202_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3202_mb : Scalar.QComplex := ((-1113589848552881744493788 : Int)/10^30,(-431476040342972965507726668 : Int)/10^30)
theorem v3202_mb_checked : Scalar.distance (sourceCoefficient 41 87 3 1) v3202_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3202_mg : Scalar.QComplex := ((-93086115168751793163223 : Int)/10^30,(240244516962631443014 : Int)/10^30)
theorem v3202_mg_checked : Scalar.distance (sourceCoefficient 41 87 3 2) v3202_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3202_upper : Scalar.QComplex := ((999994070009916688092156211874 : Int)/10^30,(-3443827086518925025049768051 : Int)/10^30)
theorem v3202_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 87 5) 1) 14) v3202_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3202 : Material (41 : Basis) (87 : Basis) where
  plus := ![v3202_pa,v3202_pb,v3202_pg]
  minus := ![(Primitive.Addresses.material3202 1).one,v3202_mb,v3202_mg]
  upper := v3202_upper
  lower := (Primitive.Addresses.material3202 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3202_pa_checked.trans (by decide +kernel)
    · exact v3202_pb_checked.trans (by decide +kernel)
    · exact v3202_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 87 Primitive.Addresses.material3202
    · exact v3202_mb_checked.trans (by decide +kernel)
    · exact v3202_mg_checked.trans (by decide +kernel)
  upper_error := v3202_upper_checked
  lower_error := reuse_lower_error 41 87 Primitive.Addresses.material3202

def v3203_pa : Scalar.QComplex := ((999998504098127628519570974992 : Int)/10^30,(-1729682487342850185899912634 : Int)/10^30)
theorem v3203_pa_checked : Scalar.distance (sourceCoefficient 41 88 1 0) v3203_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3203_pb : Scalar.QComplex := ((-746319033983320613101626 : Int)/10^30,(-431476830588589048597441429 : Int)/10^30)
theorem v3203_pb_checked : Scalar.distance (sourceCoefficient 41 88 1 1) v3203_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3203_pg : Scalar.QComplex := ((-93086285798568770482331 : Int)/10^30,(161009959212675319056 : Int)/10^30)
theorem v3203_pg_checked : Scalar.distance (sourceCoefficient 41 88 1 2) v3203_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3203_mb : Scalar.QComplex := ((-1118663827897525120971121 : Int)/10^30,(-431476025890332189059624645 : Int)/10^30)
theorem v3203_mb_checked : Scalar.distance (sourceCoefficient 41 88 3 1) v3203_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3203_mg : Scalar.QComplex := ((-93086112193947133081174 : Int)/10^30,(241339171454792551704 : Int)/10^30)
theorem v3203_mg_checked : Scalar.distance (sourceCoefficient 41 88 3 2) v3203_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3203_upper : Scalar.QComplex := ((999994029442766266067273700529 : Int)/10^30,(-3455586610101703724913671587 : Int)/10^30)
theorem v3203_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 88 5) 1) 14) v3203_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3203 : Material (41 : Basis) (88 : Basis) where
  plus := ![v3203_pa,v3203_pb,v3203_pg]
  minus := ![(Primitive.Addresses.material3203 1).one,v3203_mb,v3203_mg]
  upper := v3203_upper
  lower := (Primitive.Addresses.material3203 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3203_pa_checked.trans (by decide +kernel)
    · exact v3203_pb_checked.trans (by decide +kernel)
    · exact v3203_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 88 Primitive.Addresses.material3203
    · exact v3203_mb_checked.trans (by decide +kernel)
    · exact v3203_mg_checked.trans (by decide +kernel)
  upper_error := v3203_upper_checked
  lower_error := reuse_lower_error 41 88 Primitive.Addresses.material3203

def v3204_pa : Scalar.QComplex := ((999998476138992449763983904985 : Int)/10^30,(-1745771947577375210519464003 : Int)/10^30)
theorem v3204_pa_checked : Scalar.distance (sourceCoefficient 41 89 1 0) v3204_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3204_pb : Scalar.QComplex := ((-753261270449154789690916 : Int)/10^30,(-431476816676417951747657455 : Int)/10^30)
theorem v3204_pb_checked : Scalar.distance (sourceCoefficient 41 89 1 1) v3204_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3204_pg : Scalar.QComplex := ((-93086282996563385699947 : Int)/10^30,(162507669198749688251 : Int)/10^30)
theorem v3204_pg_checked : Scalar.distance (sourceCoefficient 41 89 1 2) v3204_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3204_mb : Scalar.QComplex := ((-1125606049772870309795173 : Int)/10^30,(-431476005987328869055750070 : Int)/10^30)
theorem v3204_mb_checked : Scalar.distance (sourceCoefficient 41 89 3 1) v3204_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3204_mg : Scalar.QComplex := ((-93086108099486527985021 : Int)/10^30,(242836878465196594926 : Int)/10^30)
theorem v3204_mg_checked : Scalar.distance (sourceCoefficient 41 89 3 2) v3204_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3204_upper : Scalar.QComplex := ((999993973714723988799547945565 : Int)/10^30,(-3471675998117936845370405291 : Int)/10^30)
theorem v3204_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 89 5) 1) 14) v3204_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3204 : Material (41 : Basis) (89 : Basis) where
  plus := ![v3204_pa,v3204_pb,v3204_pg]
  minus := ![(Primitive.Addresses.material3204 1).one,v3204_mb,v3204_mg]
  upper := v3204_upper
  lower := (Primitive.Addresses.material3204 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3204_pa_checked.trans (by decide +kernel)
    · exact v3204_pb_checked.trans (by decide +kernel)
    · exact v3204_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 89 Primitive.Addresses.material3204
    · exact v3204_mb_checked.trans (by decide +kernel)
    · exact v3204_mg_checked.trans (by decide +kernel)
  upper_error := v3204_upper_checked
  lower_error := reuse_lower_error 41 89 Primitive.Addresses.material3204

def v3205_pa : Scalar.QComplex := ((999998430051335370246666647580 : Int)/10^30,(-1771974848726893497483424850 : Int)/10^30)
theorem v3205_pa_checked : Scalar.distance (sourceCoefficient 41 90 1 0) v3205_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3205_pb : Scalar.QComplex := ((-764567226578126333174493 : Int)/10^30,(-431476793700624960290081697 : Int)/10^30)
theorem v3205_pb_checked : Scalar.distance (sourceCoefficient 41 90 1 1) v3205_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3205_pg : Scalar.QComplex := ((-93086278373110985310678 : Int)/10^30,(164946802996755935641 : Int)/10^30)
theorem v3205_pg_checked : Scalar.distance (sourceCoefficient 41 90 1 2) v3205_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3205_mb : Scalar.QComplex := ((-1136911981865043118416860 : Int)/10^30,(-431475973255013494595114437 : Int)/10^30)
theorem v3205_mb_checked : Scalar.distance (sourceCoefficient 41 90 3 1) v3205_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3205_mg : Scalar.QComplex := ((-93086101371173235947263 : Int)/10^30,(245276007365170666427 : Int)/10^30)
theorem v3205_mg_checked : Scalar.distance (sourceCoefficient 41 90 3 2) v3205_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3205_upper : Scalar.QComplex := ((999993882403305275988381595405 : Int)/10^30,(-3497878780698196799457113921 : Int)/10^30)
theorem v3205_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 90 5) 1) 14) v3205_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3205 : Material (41 : Basis) (90 : Basis) where
  plus := ![v3205_pa,v3205_pb,v3205_pg]
  minus := ![(Primitive.Addresses.material3205 1).one,v3205_mb,v3205_mg]
  upper := v3205_upper
  lower := (Primitive.Addresses.material3205 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3205_pa_checked.trans (by decide +kernel)
    · exact v3205_pb_checked.trans (by decide +kernel)
    · exact v3205_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 90 Primitive.Addresses.material3205
    · exact v3205_mb_checked.trans (by decide +kernel)
    · exact v3205_mg_checked.trans (by decide +kernel)
  upper_error := v3205_upper_checked
  lower_error := reuse_lower_error 41 90 Primitive.Addresses.material3205

def v3206_pa : Scalar.QComplex := ((999998403786144403097242352049 : Int)/10^30,(-1786735896347060218139122965 : Int)/10^30)
theorem v3206_pa_checked : Scalar.distance (sourceCoefficient 41 91 1 0) v3206_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3206_pb : Scalar.QComplex := ((-770936282888140358530735 : Int)/10^30,(-431476780583589621079834889 : Int)/10^30)
theorem v3206_pb_checked : Scalar.distance (sourceCoefficient 41 91 1 1) v3206_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3206_pg : Scalar.QComplex := ((-93086275735718015108388 : Int)/10^30,(166320855797922229469 : Int)/10^30)
theorem v3206_pg_checked : Scalar.distance (sourceCoefficient 41 91 1 2) v3206_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3206_mb : Scalar.QComplex := ((-1143281024484155670904702 : Int)/10^30,(-431475954641774295562267996 : Int)/10^30)
theorem v3206_mb_checked : Scalar.distance (sourceCoefficient 41 91 3 1) v3206_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3206_mg : Scalar.QComplex := ((-93086097548035565401283 : Int)/10^30,(246650057378762955551 : Int)/10^30)
theorem v3206_mg_checked : Scalar.distance (sourceCoefficient 41 91 3 2) v3206_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3206_upper : Scalar.QComplex := ((999993830661924347127351316142 : Int)/10^30,(-3512639761002180194543141277 : Int)/10^30)
theorem v3206_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 91 5) 1) 14) v3206_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3206 : Material (41 : Basis) (91 : Basis) where
  plus := ![v3206_pa,v3206_pb,v3206_pg]
  minus := ![(Primitive.Addresses.material3206 1).one,v3206_mb,v3206_mg]
  upper := v3206_upper
  lower := (Primitive.Addresses.material3206 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3206_pa_checked.trans (by decide +kernel)
    · exact v3206_pb_checked.trans (by decide +kernel)
    · exact v3206_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 91 Primitive.Addresses.material3206
    · exact v3206_mb_checked.trans (by decide +kernel)
    · exact v3206_mg_checked.trans (by decide +kernel)
  upper_error := v3206_upper_checked
  lower_error := reuse_lower_error 41 91 Primitive.Addresses.material3206

def v3207_pa : Scalar.QComplex := ((999998346178429650466571428082 : Int)/10^30,(-1818691949059345317622992111 : Int)/10^30)
theorem v3207_pa_checked : Scalar.distance (sourceCoefficient 41 92 1 0) v3207_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3207_pb : Scalar.QComplex := ((-784724592421570704970696 : Int)/10^30,(-431476751757208581314880765 : Int)/10^30)
theorem v3207_pb_checked : Scalar.distance (sourceCoefficient 41 92 1 1) v3207_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3207_pg : Scalar.QComplex := ((-93086269944985755678225 : Int)/10^30,(169295529701509285134 : Int)/10^30)
theorem v3207_pg_checked : Scalar.distance (sourceCoefficient 41 92 1 2) v3207_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3207_mb : Scalar.QComplex := ((-1157069304007699675862498 : Int)/10^30,(-431475913916713864234709386 : Int)/10^30)
theorem v3207_mb_checked : Scalar.distance (sourceCoefficient 41 92 3 1) v3207_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3207_mg : Scalar.QComplex := ((-93086089190295857669017 : Int)/10^30,(249624725177601832608 : Int)/10^30)
theorem v3207_mg_checked : Scalar.distance (sourceCoefficient 41 92 3 2) v3207_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3207_upper : Scalar.QComplex := ((999993717901047443472720546774 : Int)/10^30,(-3544595666693989068739053237 : Int)/10^30)
theorem v3207_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 92 5) 1) 14) v3207_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3207 : Material (41 : Basis) (92 : Basis) where
  plus := ![v3207_pa,v3207_pb,v3207_pg]
  minus := ![(Primitive.Addresses.material3207 1).one,v3207_mb,v3207_mg]
  upper := v3207_upper
  lower := (Primitive.Addresses.material3207 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3207_pa_checked.trans (by decide +kernel)
    · exact v3207_pb_checked.trans (by decide +kernel)
    · exact v3207_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 92 Primitive.Addresses.material3207
    · exact v3207_mb_checked.trans (by decide +kernel)
    · exact v3207_mg_checked.trans (by decide +kernel)
  upper_error := v3207_upper_checked
  lower_error := reuse_lower_error 41 92 Primitive.Addresses.material3207

def v3208_pa : Scalar.QComplex := ((999998276484250183136623929957 : Int)/10^30,(-1856617496720093631186152120 : Int)/10^30)
theorem v3208_pa_checked : Scalar.distance (sourceCoefficient 41 93 1 0) v3208_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3208_pb : Scalar.QComplex := ((-801088602496595783479251 : Int)/10^30,(-431476716783600075507840126 : Int)/10^30)
theorem v3208_pb_checked : Scalar.distance (sourceCoefficient 41 93 1 1) v3208_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3208_pg : Scalar.QComplex := ((-93086262928612920530168 : Int)/10^30,(172825882325679936659 : Int)/10^30)
theorem v3208_pg_checked : Scalar.distance (sourceCoefficient 41 93 1 2) v3208_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3208_mb : Scalar.QComplex := ((-1173433277809006943576353 : Int)/10^30,(-431475864821714693608614539 : Int)/10^30)
theorem v3208_mb_checked : Scalar.distance (sourceCoefficient 41 93 3 1) v3208_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3208_mg : Scalar.QComplex := ((-93086079127390321557750 : Int)/10^30,(253155070432447106038 : Int)/10^30)
theorem v3208_mg_checked : Scalar.distance (sourceCoefficient 41 93 3 2) v3208_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3208_upper : Scalar.QComplex := ((999993582750917093792103384003 : Int)/10^30,(-3582521037583258035356164023 : Int)/10^30)
theorem v3208_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 93 5) 1) 14) v3208_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3208 : Material (41 : Basis) (93 : Basis) where
  plus := ![v3208_pa,v3208_pb,v3208_pg]
  minus := ![(Primitive.Addresses.material3208 1).one,v3208_mb,v3208_mg]
  upper := v3208_upper
  lower := (Primitive.Addresses.material3208 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3208_pa_checked.trans (by decide +kernel)
    · exact v3208_pb_checked.trans (by decide +kernel)
    · exact v3208_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 93 Primitive.Addresses.material3208
    · exact v3208_mb_checked.trans (by decide +kernel)
    · exact v3208_mg_checked.trans (by decide +kernel)
  upper_error := v3208_upper_checked
  lower_error := reuse_lower_error 41 93 Primitive.Addresses.material3208

def v3209_pa : Scalar.QComplex := ((999998192307010887265721147013 : Int)/10^30,(-1901415975127884968821082888 : Int)/10^30)
theorem v3209_pa_checked : Scalar.distance (sourceCoefficient 41 94 1 0) v3209_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3209_pb : Scalar.QComplex := ((-820418124674715025998470 : Int)/10^30,(-431476674406000785517503779 : Int)/10^30)
theorem v3209_pb_checked : Scalar.distance (sourceCoefficient 41 94 1 1) v3209_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3209_pg : Scalar.QComplex := ((-93086254439487980375125 : Int)/10^30,(176996011210510015610 : Int)/10^30)
theorem v3209_pg_checked : Scalar.distance (sourceCoefficient 41 94 1 2) v3209_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3209_mb : Scalar.QComplex := ((-1192762756219902105336451 : Int)/10^30,(-431475805763624112380188229 : Int)/10^30)
theorem v3209_mb_checked : Scalar.distance (sourceCoefficient 41 94 3 1) v3209_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3209_mg : Scalar.QComplex := ((-93086067039635130316465 : Int)/10^30,(257325190438815129503 : Int)/10^30)
theorem v3209_mg_checked : Scalar.distance (sourceCoefficient 41 94 3 2) v3209_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3209_upper : Scalar.QComplex := ((999993421255693524397385453456 : Int)/10^30,(-3627319303986699658345722707 : Int)/10^30)
theorem v3209_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 94 5) 1) 14) v3209_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3209 : Material (41 : Basis) (94 : Basis) where
  plus := ![v3209_pa,v3209_pb,v3209_pg]
  minus := ![(Primitive.Addresses.material3209 1).one,v3209_mb,v3209_mg]
  upper := v3209_upper
  lower := (Primitive.Addresses.material3209 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3209_pa_checked.trans (by decide +kernel)
    · exact v3209_pb_checked.trans (by decide +kernel)
    · exact v3209_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 94 Primitive.Addresses.material3209
    · exact v3209_mb_checked.trans (by decide +kernel)
    · exact v3209_mg_checked.trans (by decide +kernel)
  upper_error := v3209_upper_checked
  lower_error := reuse_lower_error 41 94 Primitive.Addresses.material3209

def v3210_pa : Scalar.QComplex := ((999998107143193065583080378639 : Int)/10^30,(-1945690116889619779641931993 : Int)/10^30)
theorem v3210_pa_checked : Scalar.distance (sourceCoefficient 41 95 1 0) v3210_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3210_pb : Scalar.QComplex := ((-839521406458180240218037 : Int)/10^30,(-431476631390011806463009901 : Int)/10^30)
theorem v3210_pb_checked : Scalar.distance (sourceCoefficient 41 95 1 1) v3210_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3210_pg : Scalar.QComplex := ((-93086245835581798112309 : Int)/10^30,(181117331369822568370 : Int)/10^30)
theorem v3210_pg_checked : Scalar.distance (sourceCoefficient 41 95 1 2) v3210_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3210_mb : Scalar.QComplex := ((-1211865993769481327765321 : Int)/10^30,(-431475746262379350886564298 : Int)/10^30)
theorem v3210_mb_checked : Scalar.distance (sourceCoefficient 41 95 3 1) v3210_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3210_mg : Scalar.QComplex := ((-93086054879218471563941 : Int)/10^30,(261446501638788303570 : Int)/10^30)
theorem v3210_mg_checked : Scalar.distance (sourceCoefficient 41 95 3 2) v3210_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3210_upper : Scalar.QComplex := ((999993259678850382228363632175 : Int)/10^30,(-3671593232822277562066937664 : Int)/10^30)
theorem v3210_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 95 5) 1) 14) v3210_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3210 : Material (41 : Basis) (95 : Basis) where
  plus := ![v3210_pa,v3210_pb,v3210_pg]
  minus := ![(Primitive.Addresses.material3210 1).one,v3210_mb,v3210_mg]
  upper := v3210_upper
  lower := (Primitive.Addresses.material3210 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3210_pa_checked.trans (by decide +kernel)
    · exact v3210_pb_checked.trans (by decide +kernel)
    · exact v3210_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 95 Primitive.Addresses.material3210
    · exact v3210_mb_checked.trans (by decide +kernel)
    · exact v3210_mg_checked.trans (by decide +kernel)
  upper_error := v3210_upper_checked
  lower_error := reuse_lower_error 41 95 Primitive.Addresses.material3210

def v3211_pa : Scalar.QComplex := ((999998065543769899111370679522 : Int)/10^30,(-1966954172847163992232833123 : Int)/10^30)
theorem v3211_pa_checked : Scalar.distance (sourceCoefficient 41 96 1 0) v3211_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3211_pb : Scalar.QComplex := ((-848696360939224114539077 : Int)/10^30,(-431476610329348224358540451 : Int)/10^30)
theorem v3211_pb_checked : Scalar.distance (sourceCoefficient 41 96 1 1) v3211_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3211_pg : Scalar.QComplex := ((-93086241627610061489634 : Int)/10^30,(183096725596688534502 : Int)/10^30)
theorem v3211_pg_checked : Scalar.distance (sourceCoefficient 41 96 1 2) v3211_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3211_mb : Scalar.QComplex := ((-1221040926659866198379534 : Int)/10^30,(-431475717284151118099010442 : Int)/10^30)
theorem v3211_mb_checked : Scalar.distance (sourceCoefficient 41 96 3 1) v3211_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3211_mg : Scalar.QComplex := ((-93086048963120232582754 : Int)/10^30,(263425891497345247562 : Int)/10^30)
theorem v3211_mg_checked : Scalar.distance (sourceCoefficient 41 96 3 2) v3211_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3211_upper : Scalar.QComplex := ((999993181379657650577015919445 : Int)/10^30,(-3692857185312677762232638724 : Int)/10^30)
theorem v3211_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 96 5) 1) 14) v3211_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3211 : Material (41 : Basis) (96 : Basis) where
  plus := ![v3211_pa,v3211_pb,v3211_pg]
  minus := ![(Primitive.Addresses.material3211 1).one,v3211_mb,v3211_mg]
  upper := v3211_upper
  lower := (Primitive.Addresses.material3211 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3211_pa_checked.trans (by decide +kernel)
    · exact v3211_pb_checked.trans (by decide +kernel)
    · exact v3211_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 96 Primitive.Addresses.material3211
    · exact v3211_mb_checked.trans (by decide +kernel)
    · exact v3211_mg_checked.trans (by decide +kernel)
  upper_error := v3211_upper_checked
  lower_error := reuse_lower_error 41 96 Primitive.Addresses.material3211

def v3212_pa : Scalar.QComplex := ((999997918960679326848848759590 : Int)/10^30,(-2040116249291115301446148891 : Int)/10^30)
theorem v3212_pa_checked : Scalar.distance (sourceCoefficient 41 97 1 0) v3212_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3212_pb : Scalar.QComplex := ((-880264123900573664383509 : Int)/10^30,(-431476535879848201521545720 : Int)/10^30)
theorem v3212_pb_checked : Scalar.distance (sourceCoefficient 41 97 1 1) v3212_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3212_pg : Scalar.QComplex := ((-93086226774339933537292 : Int)/10^30,(189907119031710560373 : Int)/10^30)
theorem v3212_pg_checked : Scalar.distance (sourceCoefficient 41 97 1 2) v3212_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3212_mb : Scalar.QComplex := ((-1252608613620529440974962 : Int)/10^30,(-431475615593121139834317320 : Int)/10^30)
theorem v3212_mb_checked : Scalar.distance (sourceCoefficient 41 97 3 1) v3212_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3212_mg : Scalar.QComplex := ((-93086028232792829491708 : Int)/10^30,(270236269578843393249 : Int)/10^30)
theorem v3212_mg_checked : Scalar.distance (sourceCoefficient 41 97 3 2) v3212_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3212_upper : Scalar.QComplex := ((999992908525678666077024831766 : Int)/10^30,(-3766018899801194015764697173 : Int)/10^30)
theorem v3212_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 97 5) 1) 14) v3212_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3212 : Material (41 : Basis) (97 : Basis) where
  plus := ![v3212_pa,v3212_pb,v3212_pg]
  minus := ![(Primitive.Addresses.material3212 1).one,v3212_mb,v3212_mg]
  upper := v3212_upper
  lower := (Primitive.Addresses.material3212 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3212_pa_checked.trans (by decide +kernel)
    · exact v3212_pb_checked.trans (by decide +kernel)
    · exact v3212_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 97 Primitive.Addresses.material3212
    · exact v3212_mb_checked.trans (by decide +kernel)
    · exact v3212_mg_checked.trans (by decide +kernel)
  upper_error := v3212_upper_checked
  lower_error := reuse_lower_error 41 97 Primitive.Addresses.material3212

def v3213_pa : Scalar.QComplex := ((999999521957415206927081051440 : Int)/10^30,(-977795960853506983975641759 : Int)/10^30)
theorem v3213_pa_checked : Scalar.distance (sourceCoefficient 42 43 1 0) v3213_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3213_pb : Scalar.QComplex := ((-421896977216677343684628 : Int)/10^30,(-431477314718795664793345272 : Int)/10^30)
theorem v3213_pb_checked : Scalar.distance (sourceCoefficient 42 43 1 1) v3213_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3213_pg : Scalar.QComplex := ((-93086385395840163662132 : Int)/10^30,(91019535161719248255 : Int)/10^30)
theorem v3213_pg_checked : Scalar.distance (sourceCoefficient 42 43 1 2) v3213_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3213_mb : Scalar.QComplex := ((-794242309710604300918445 : Int)/10^30,(-431476789981982104031801047 : Int)/10^30)
theorem v3213_mb_checked : Scalar.distance (sourceCoefficient 42 43 3 1) v3213_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3213_mg : Scalar.QComplex := ((-93086272189765145937932 : Int)/10^30,(171348859412429593200 : Int)/10^30)
theorem v3213_mg_checked : Scalar.distance (sourceCoefficient 42 43 3 2) v3213_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3213_upper : Scalar.QComplex := ((999996344988471970387406653747 : Int)/10^30,(-2703702960191809820205284472 : Int)/10^30)
theorem v3213_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 43 5) 1) 14) v3213_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3213 : Material (42 : Basis) (43 : Basis) where
  plus := ![v3213_pa,v3213_pb,v3213_pg]
  minus := ![(Primitive.Addresses.material3213 1).one,v3213_mb,v3213_mg]
  upper := v3213_upper
  lower := (Primitive.Addresses.material3213 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3213_pa_checked.trans (by decide +kernel)
    · exact v3213_pb_checked.trans (by decide +kernel)
    · exact v3213_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 43 Primitive.Addresses.material3213
    · exact v3213_mb_checked.trans (by decide +kernel)
    · exact v3213_mg_checked.trans (by decide +kernel)
  upper_error := v3213_upper_checked
  lower_error := reuse_lower_error 42 43 Primitive.Addresses.material3213

def v3214_pa : Scalar.QComplex := ((999999516214512668948518793523 : Int)/10^30,(-983651737462860993786737339 : Int)/10^30)
theorem v3214_pa_checked : Scalar.distance (sourceCoefficient 42 44 1 0) v3214_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3214_pb : Scalar.QComplex := ((-424423613176266070084163 : Int)/10^30,(-431477312225360831407284055 : Int)/10^30)
theorem v3214_pb_checked : Scalar.distance (sourceCoefficient 42 44 1 1) v3214_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3214_pg : Scalar.QComplex := ((-93086384859581733734292 : Int)/10^30,(91564628498902550714 : Int)/10^30)
theorem v3214_pg_checked : Scalar.distance (sourceCoefficient 42 44 1 2) v3214_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3214_mb : Scalar.QComplex := ((-796768942577689025519212 : Int)/10^30,(-431476785308175161399746880 : Int)/10^30)
theorem v3214_mb_checked : Scalar.distance (sourceCoefficient 42 44 3 1) v3214_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3214_mg : Scalar.QComplex := ((-93086271183115915786988 : Int)/10^30,(171893952083882861385 : Int)/10^30)
theorem v3214_mg_checked : Scalar.distance (sourceCoefficient 42 44 3 2) v3214_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3214_upper : Scalar.QComplex := ((999996329139038789946789751897 : Int)/10^30,(-2709558718167943649721677932 : Int)/10^30)
theorem v3214_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 44 5) 1) 14) v3214_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3214 : Material (42 : Basis) (44 : Basis) where
  plus := ![v3214_pa,v3214_pb,v3214_pg]
  minus := ![(Primitive.Addresses.material3214 1).one,v3214_mb,v3214_mg]
  upper := v3214_upper
  lower := (Primitive.Addresses.material3214 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3214_pa_checked.trans (by decide +kernel)
    · exact v3214_pb_checked.trans (by decide +kernel)
    · exact v3214_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 44 Primitive.Addresses.material3214
    · exact v3214_mb_checked.trans (by decide +kernel)
    · exact v3214_mg_checked.trans (by decide +kernel)
  upper_error := v3214_upper_checked
  lower_error := reuse_lower_error 42 44 Primitive.Addresses.material3214

def v3215_pa : Scalar.QComplex := ((999999513344573279014095436627 : Int)/10^30,(-986565059490993453529955953 : Int)/10^30)
theorem v3215_pa_checked : Scalar.distance (sourceCoefficient 42 45 1 0) v3215_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3215_pb : Scalar.QComplex := ((-425680646133324840840034 : Int)/10^30,(-431477310977497141346838705 : Int)/10^30)
theorem v3215_pb_checked : Scalar.distance (sourceCoefficient 42 45 1 1) v3215_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3215_pg : Scalar.QComplex := ((-93086384591399238680501 : Int)/10^30,(91835819244615089008 : Int)/10^30)
theorem v3215_pg_checked : Scalar.distance (sourceCoefficient 42 45 1 2) v3215_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3215_mb : Scalar.QComplex := ((-798025973989846814290046 : Int)/10^30,(-431476782975549108697015223 : Int)/10^30)
theorem v3215_mb_checked : Scalar.distance (sourceCoefficient 42 45 3 1) v3215_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3215_mg : Scalar.QComplex := ((-93086270680908121017659 : Int)/10^30,(172165142497189276281 : Int)/10^30)
theorem v3215_mg_checked : Scalar.distance (sourceCoefficient 42 45 3 2) v3215_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3215_upper : Scalar.QComplex := ((999996321240974148403172188307 : Int)/10^30,(-2712472030903770143247694184 : Int)/10^30)
theorem v3215_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 45 5) 1) 14) v3215_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3215 : Material (42 : Basis) (45 : Basis) where
  plus := ![v3215_pa,v3215_pb,v3215_pg]
  minus := ![(Primitive.Addresses.material3215 1).one,v3215_mb,v3215_mg]
  upper := v3215_upper
  lower := (Primitive.Addresses.material3215 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3215_pa_checked.trans (by decide +kernel)
    · exact v3215_pb_checked.trans (by decide +kernel)
    · exact v3215_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 45 Primitive.Addresses.material3215
    · exact v3215_mb_checked.trans (by decide +kernel)
    · exact v3215_mg_checked.trans (by decide +kernel)
  upper_error := v3215_upper_checked
  lower_error := reuse_lower_error 42 45 Primitive.Addresses.material3215

def v3216_pa : Scalar.QComplex := ((999999497066288514169862142570 : Int)/10^30,(-1002929294631153012469629303 : Int)/10^30)
theorem v3216_pa_checked : Scalar.distance (sourceCoefficient 42 46 1 0) v3216_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3216_pb : Scalar.QComplex := ((-432741445667432263137064 : Int)/10^30,(-431477303877458264487702382 : Int)/10^30)
theorem v3216_pb_checked : Scalar.distance (sourceCoefficient 42 46 1 1) v3216_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3216_pg : Scalar.QComplex := ((-93086383067878702908761 : Int)/10^30,(93359107463475310289 : Int)/10^30)
theorem v3216_pg_checked : Scalar.distance (sourceCoefficient 42 46 1 2) v3216_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3216_mb : Scalar.QComplex := ((-805086764767882098709758 : Int)/10^30,(-431476769782360884178191203 : Int)/10^30)
theorem v3216_mb_checked : Scalar.distance (sourceCoefficient 42 46 3 1) v3216_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3216_mg : Scalar.QComplex := ((-93086267842859026000461 : Int)/10^30,(173688428834130070416 : Int)/10^30)
theorem v3216_mg_checked : Scalar.distance (sourceCoefficient 42 46 3 2) v3216_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3216_upper : Scalar.QComplex := ((999996276719528328051748649805 : Int)/10^30,(-2728836213576480989348885973 : Int)/10^30)
theorem v3216_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 46 5) 1) 14) v3216_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3216 : Material (42 : Basis) (46 : Basis) where
  plus := ![v3216_pa,v3216_pb,v3216_pg]
  minus := ![(Primitive.Addresses.material3216 1).one,v3216_mb,v3216_mg]
  upper := v3216_upper
  lower := (Primitive.Addresses.material3216 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3216_pa_checked.trans (by decide +kernel)
    · exact v3216_pb_checked.trans (by decide +kernel)
    · exact v3216_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 46 Primitive.Addresses.material3216
    · exact v3216_mb_checked.trans (by decide +kernel)
    · exact v3216_mg_checked.trans (by decide +kernel)
  upper_error := v3216_upper_checked
  lower_error := reuse_lower_error 42 46 Primitive.Addresses.material3216

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
