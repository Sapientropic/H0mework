import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B136

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3265_pa : Scalar.QComplex := ((999998084342177130486460432861 : Int)/10^30,(-1957373744585875648086377081 : Int)/10^30)
theorem v3265_pa_checked : Scalar.distance (sourceCoefficient 42 95 1 0) v3265_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3265_pb : Scalar.QComplex := ((-844562631613433830744300 : Int)/10^30,(-431476623233804872645431735 : Int)/10^30)
theorem v3265_pb_checked : Scalar.distance (sourceCoefficient 42 95 1 1) v3265_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3265_pg : Scalar.QComplex := ((-93086243894544188679083 : Int)/10^30,(182204918823576172926 : Int)/10^30)
theorem v3265_pg_checked : Scalar.distance (sourceCoefficient 42 95 1 2) v3265_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3265_mb : Scalar.QComplex := ((-1216907210009217155658671 : Int)/10^30,(-431475733755825193366297632 : Int)/10^30)
theorem v3265_mb_checked : Scalar.distance (sourceCoefficient 42 95 3 1) v3265_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3265_mg : Scalar.QComplex := ((-93086051999642595398944 : Int)/10^30,(262534087012555358040 : Int)/10^30)
theorem v3265_mg_checked : Scalar.distance (sourceCoefficient 42 95 3 2) v3265_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3265_upper : Scalar.QComplex := ((999993216712986933253836829977 : Int)/10^30,(-3683276803764657420287889855 : Int)/10^30)
theorem v3265_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 95 5) 1) 14) v3265_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3265 : Material (42 : Basis) (95 : Basis) where
  plus := ![v3265_pa,v3265_pb,v3265_pg]
  minus := ![(Primitive.Addresses.material3265 1).one,v3265_mb,v3265_mg]
  upper := v3265_upper
  lower := (Primitive.Addresses.material3265 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3265_pa_checked.trans (by decide +kernel)
    · exact v3265_pb_checked.trans (by decide +kernel)
    · exact v3265_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 95 Primitive.Addresses.material3265
    · exact v3265_mb_checked.trans (by decide +kernel)
    · exact v3265_mg_checked.trans (by decide +kernel)
  upper_error := v3265_upper_checked
  lower_error := reuse_lower_error 42 95 Primitive.Addresses.material3265

def v3266_pa : Scalar.QComplex := ((999998042494312180645162681743 : Int)/10^30,(-1978637800055935409074846420 : Int)/10^30)
theorem v3266_pa_checked : Scalar.distance (sourceCoefficient 42 96 1 0) v3266_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3266_pb : Scalar.QComplex := ((-853737585954251998481907 : Int)/10^30,(-431476602101676601762836620 : Int)/10^30)
theorem v3266_pb_checked : Scalar.distance (sourceCoefficient 42 96 1 1) v3266_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3266_pg : Scalar.QComplex := ((-93086239667300321042312 : Int)/10^30,(184184313012626985379 : Int)/10^30)
theorem v3266_pg_checked : Scalar.distance (sourceCoefficient 42 96 1 2) v3266_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3266_mb : Scalar.QComplex := ((-1226082142697705564136469 : Int)/10^30,(-431475704706132419418657091 : Int)/10^30)
theorem v3266_mb_checked : Scalar.distance (sourceCoefficient 42 96 3 1) v3266_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3266_mg : Scalar.QComplex := ((-93086046064272265212330 : Int)/10^30,(264513476816666181352 : Int)/10^30)
theorem v3266_mg_checked : Scalar.distance (sourceCoefficient 42 96 3 2) v3266_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3266_upper : Scalar.QComplex := ((999993138165353629611692594116 : Int)/10^30,(-3704540755338785915268603344 : Int)/10^30)
theorem v3266_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 96 5) 1) 14) v3266_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3266 : Material (42 : Basis) (96 : Basis) where
  plus := ![v3266_pa,v3266_pb,v3266_pg]
  minus := ![(Primitive.Addresses.material3266 1).one,v3266_mb,v3266_mg]
  upper := v3266_upper
  lower := (Primitive.Addresses.material3266 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3266_pa_checked.trans (by decide +kernel)
    · exact v3266_pb_checked.trans (by decide +kernel)
    · exact v3266_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 96 Primitive.Addresses.material3266
    · exact v3266_mb_checked.trans (by decide +kernel)
    · exact v3266_mg_checked.trans (by decide +kernel)
  upper_error := v3266_upper_checked
  lower_error := reuse_lower_error 42 96 Primitive.Addresses.material3266

def v3267_pa : Scalar.QComplex := ((999997895056421528001207447798 : Int)/10^30,(-2051799874782267607739584705 : Int)/10^30)
theorem v3267_pa_checked : Scalar.distance (sourceCoefficient 42 97 1 0) v3267_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3267_pb : Scalar.QComplex := ((-885305348421525582925327 : Int)/10^30,(-431476527406291928269050901 : Int)/10^30)
theorem v3267_pb_checked : Scalar.distance (sourceCoefficient 42 97 1 1) v3267_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3267_pg : Scalar.QComplex := ((-93086224747721624460645 : Int)/10^30,(190994706314409827865 : Int)/10^30)
theorem v3267_pg_checked : Scalar.distance (sourceCoefficient 42 97 1 2) v3267_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3267_mb : Scalar.QComplex := ((-1257649828952105646014708 : Int)/10^30,(-431475602769218308416571691 : Int)/10^30)
theorem v3267_mb_checked : Scalar.distance (sourceCoefficient 42 97 3 1) v3267_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3267_mg : Scalar.QComplex := ((-93086025267636433161084 : Int)/10^30,(271323854707703884964 : Int)/10^30)
theorem v3267_mg_checked : Scalar.distance (sourceCoefficient 42 97 3 2) v3267_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3267_upper : Scalar.QComplex := ((999992864456578802309339667922 : Int)/10^30,(-3777702466634378224563159253 : Int)/10^30)
theorem v3267_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 42 97 5) 1) 14) v3267_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3267 : Material (42 : Basis) (97 : Basis) where
  plus := ![v3267_pa,v3267_pb,v3267_pg]
  minus := ![(Primitive.Addresses.material3267 1).one,v3267_mb,v3267_mg]
  upper := v3267_upper
  lower := (Primitive.Addresses.material3267 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3267_pa_checked.trans (by decide +kernel)
    · exact v3267_pb_checked.trans (by decide +kernel)
    · exact v3267_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 42 97 Primitive.Addresses.material3267
    · exact v3267_mb_checked.trans (by decide +kernel)
    · exact v3267_mg_checked.trans (by decide +kernel)
  upper_error := v3267_upper_checked
  lower_error := reuse_lower_error 42 97 Primitive.Addresses.material3267

def v3268_pa : Scalar.QComplex := ((999999500869978212283689284400 : Int)/10^30,(-999129518353178259067462355 : Int)/10^30)
theorem v3268_pa_checked : Scalar.distance (sourceCoefficient 43 44 1 0) v3268_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3268_pb : Scalar.QComplex := ((-431101927735141705497915 : Int)/10^30,(-431477305634802312685665522 : Int)/10^30)
theorem v3268_pb_checked : Scalar.distance (sourceCoefficient 43 44 1 1) v3268_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3268_pg : Scalar.QComplex := ((-93086383434478272197486 : Int)/10^30,(93005399867916809975 : Int)/10^30)
theorem v3268_pg_checked : Scalar.distance (sourceCoefficient 43 44 1 2) v3268_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3268_mb : Scalar.QComplex := ((-803447248962567762690507 : Int)/10^30,(-431476772954534412456843692 : Int)/10^30)
theorem v3268_mb_checked : Scalar.distance (sourceCoefficient 43 44 3 1) v3268_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3268_mg : Scalar.QComplex := ((-93086268514692183355658 : Int)/10^30,(173334721686631990429 : Int)/10^30)
theorem v3268_mg_checked : Scalar.distance (sourceCoefficient 43 44 3 2) v3268_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3268_upper : Scalar.QComplex := ((999996287081281503789820002023 : Int)/10^30,(-2725036449522649999824486141 : Int)/10^30)
theorem v3268_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 44 5) 1) 14) v3268_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3268 : Material (43 : Basis) (44 : Basis) where
  plus := ![v3268_pa,v3268_pb,v3268_pg]
  minus := ![(Primitive.Addresses.material3268 1).one,v3268_mb,v3268_mg]
  upper := v3268_upper
  lower := (Primitive.Addresses.material3268 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3268_pa_checked.trans (by decide +kernel)
    · exact v3268_pb_checked.trans (by decide +kernel)
    · exact v3268_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 44 Primitive.Addresses.material3268
    · exact v3268_mb_checked.trans (by decide +kernel)
    · exact v3268_mg_checked.trans (by decide +kernel)
  upper_error := v3268_upper_checked
  lower_error := reuse_lower_error 43 44 Primitive.Addresses.material3268

def v3269_pa : Scalar.QComplex := ((999999497954947040520655674890 : Int)/10^30,(-1002042840336541443403028987 : Int)/10^30)
theorem v3269_pa_checked : Scalar.distance (sourceCoefficient 43 45 1 0) v3269_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3269_pb : Scalar.QComplex := ((-432358960679322519020762 : Int)/10^30,(-431477304373967895878760053 : Int)/10^30)
theorem v3269_pb_checked : Scalar.distance (sourceCoefficient 43 45 1 1) v3269_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3269_pg : Scalar.QComplex := ((-93086383162797916322485 : Int)/10^30,(93276590610156504924 : Int)/10^30)
theorem v3269_pg_checked : Scalar.distance (sourceCoefficient 43 45 1 2) v3269_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3269_mb : Scalar.QComplex := ((-804704280350654446021021 : Int)/10^30,(-431476770608937648950343365 : Int)/10^30)
theorem v3269_mb_checked : Scalar.distance (sourceCoefficient 43 45 3 1) v3269_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3269_mg : Scalar.QComplex := ((-93086268008986532064440 : Int)/10^30,(173605912093447066922 : Int)/10^30)
theorem v3269_mg_checked : Scalar.distance (sourceCoefficient 43 45 3 2) v3269_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3269_upper : Scalar.QComplex := ((999996279138125224844212283424 : Int)/10^30,(-2727949762135882959879738605 : Int)/10^30)
theorem v3269_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 45 5) 1) 14) v3269_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3269 : Material (43 : Basis) (45 : Basis) where
  plus := ![v3269_pa,v3269_pb,v3269_pg]
  minus := ![(Primitive.Addresses.material3269 1).one,v3269_mb,v3269_mg]
  upper := v3269_upper
  lower := (Primitive.Addresses.material3269 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3269_pa_checked.trans (by decide +kernel)
    · exact v3269_pb_checked.trans (by decide +kernel)
    · exact v3269_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 45 Primitive.Addresses.material3269
    · exact v3269_mb_checked.trans (by decide +kernel)
    · exact v3269_mg_checked.trans (by decide +kernel)
  upper_error := v3269_upper_checked
  lower_error := reuse_lower_error 43 45 Primitive.Addresses.material3269

def v3270_pa : Scalar.QComplex := ((999999481423380107226913646814 : Int)/10^30,(-1018407075222789029741902712 : Int)/10^30)
theorem v3270_pa_checked : Scalar.distance (sourceCoefficient 43 46 1 0) v3270_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3270_pb : Scalar.QComplex := ((-439419760140391736115692 : Int)/10^30,(-431477297201071978038997448 : Int)/10^30)
theorem v3270_pb_checked : Scalar.distance (sourceCoefficient 43 46 1 1) v3270_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3270_pg : Scalar.QComplex := ((-93086381619629769882432 : Int)/10^30,(94799878809320260354 : Int)/10^30)
theorem v3270_pg_checked : Scalar.distance (sourceCoefficient 43 46 1 2) v3270_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3270_mb : Scalar.QComplex := ((-811765070992779207427130 : Int)/10^30,(-431476757342892473607580723 : Int)/10^30)
theorem v3270_mb_checked : Scalar.distance (sourceCoefficient 43 46 3 1) v3270_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3270_mg : Scalar.QComplex := ((-93086265151289850691796 : Int)/10^30,(175129198393736399428 : Int)/10^30)
theorem v3270_mg_checked : Scalar.distance (sourceCoefficient 43 46 3 2) v3270_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3270_upper : Scalar.QComplex := ((999996234363398051506347297697 : Int)/10^30,(-2744313944117540166387166032 : Int)/10^30)
theorem v3270_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 46 5) 1) 14) v3270_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3270 : Material (43 : Basis) (46 : Basis) where
  plus := ![v3270_pa,v3270_pb,v3270_pg]
  minus := ![(Primitive.Addresses.material3270 1).one,v3270_mb,v3270_mg]
  upper := v3270_upper
  lower := (Primitive.Addresses.material3270 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3270_pa_checked.trans (by decide +kernel)
    · exact v3270_pb_checked.trans (by decide +kernel)
    · exact v3270_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 46 Primitive.Addresses.material3270
    · exact v3270_mb_checked.trans (by decide +kernel)
    · exact v3270_mg_checked.trans (by decide +kernel)
  upper_error := v3270_upper_checked
  lower_error := reuse_lower_error 43 46 Primitive.Addresses.material3270

def v3271_pa : Scalar.QComplex := ((999999477405095469300568554031 : Int)/10^30,(-1022345115876221429234940977 : Int)/10^30)
theorem v3271_pa_checked : Scalar.distance (sourceCoefficient 43 47 1 0) v3271_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3271_pb : Scalar.QComplex := ((-441118936143262064776403 : Int)/10^30,(-431477295451921919538251997 : Int)/10^30)
theorem v3271_pb_checked : Scalar.distance (sourceCoefficient 43 47 1 1) v3271_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3271_pg : Scalar.QComplex := ((-93086381243926142713818 : Int)/10^30,(95166456952825283227 : Int)/10^30)
theorem v3271_pg_checked : Scalar.distance (sourceCoefficient 43 47 1 2) v3271_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3271_mb : Scalar.QComplex := ((-813464244853530932347678 : Int)/10^30,(-431476754127430703964563189 : Int)/10^30)
theorem v3271_mb_checked : Scalar.distance (sourceCoefficient 43 47 3 1) v3271_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3271_mg : Scalar.QComplex := ((-93086264459245935636679 : Int)/10^30,(175495776076532316842 : Int)/10^30)
theorem v3271_mg_checked : Scalar.distance (sourceCoefficient 43 47 3 2) v3271_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3271_upper : Scalar.QComplex := ((999996223548418486775974655805 : Int)/10^30,(-2748251971970528858217188900 : Int)/10^30)
theorem v3271_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 47 5) 1) 14) v3271_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3271 : Material (43 : Basis) (47 : Basis) where
  plus := ![v3271_pa,v3271_pb,v3271_pg]
  minus := ![(Primitive.Addresses.material3271 1).one,v3271_mb,v3271_mg]
  upper := v3271_upper
  lower := (Primitive.Addresses.material3271 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3271_pa_checked.trans (by decide +kernel)
    · exact v3271_pb_checked.trans (by decide +kernel)
    · exact v3271_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 47 Primitive.Addresses.material3271
    · exact v3271_mb_checked.trans (by decide +kernel)
    · exact v3271_mg_checked.trans (by decide +kernel)
  upper_error := v3271_upper_checked
  lower_error := reuse_lower_error 43 47 Primitive.Addresses.material3271

def v3272_pa : Scalar.QComplex := ((999999448985370604160568126670 : Int)/10^30,(-1049775668976261354230252840 : Int)/10^30)
theorem v3272_pa_checked : Scalar.distance (sourceCoefficient 43 48 1 0) v3272_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3272_pb : Scalar.QComplex := ((-452954603015671602138446 : Int)/10^30,(-431477283020646551770961825 : Int)/10^30)
theorem v3272_pb_checked : Scalar.distance (sourceCoefficient 43 48 1 1) v3272_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3272_pg : Scalar.QComplex := ((-93086378580226747654501 : Int)/10^30,(97719869191712566905 : Int)/10^30)
theorem v3272_pg_checked : Scalar.distance (sourceCoefficient 43 48 1 2) v3272_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3272_mb : Scalar.QComplex := ((-825299896591350017889282 : Int)/10^30,(-431476731482512512687665214 : Int)/10^30)
theorem v3272_mb_checked : Scalar.distance (sourceCoefficient 43 48 3 1) v3272_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3272_mg : Scalar.QComplex := ((-93086259592067771652844 : Int)/10^30,(178049185066014917910 : Int)/10^30)
theorem v3272_mg_checked : Scalar.distance (sourceCoefficient 43 48 3 2) v3272_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3272_upper : Scalar.QComplex := ((999996147786089779147128916103 : Int)/10^30,(-2775682435166115259886907126 : Int)/10^30)
theorem v3272_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 48 5) 1) 14) v3272_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3272 : Material (43 : Basis) (48 : Basis) where
  plus := ![v3272_pa,v3272_pb,v3272_pg]
  minus := ![(Primitive.Addresses.material3272 1).one,v3272_mb,v3272_mg]
  upper := v3272_upper
  lower := (Primitive.Addresses.material3272 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3272_pa_checked.trans (by decide +kernel)
    · exact v3272_pb_checked.trans (by decide +kernel)
    · exact v3272_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 48 Primitive.Addresses.material3272
    · exact v3272_mb_checked.trans (by decide +kernel)
    · exact v3272_mg_checked.trans (by decide +kernel)
  upper_error := v3272_upper_checked
  lower_error := reuse_lower_error 43 48 Primitive.Addresses.material3272

def v3273_pa : Scalar.QComplex := ((999999425607166178149972489065 : Int)/10^30,(-1071814040641646245236132244 : Int)/10^30)
theorem v3273_pa_checked : Scalar.distance (sourceCoefficient 43 49 1 0) v3273_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3273_pb : Scalar.QComplex := ((-462463664754292564096013 : Int)/10^30,(-431477272719455936866358510 : Int)/10^30)
theorem v3273_pb_checked : Scalar.distance (sourceCoefficient 43 49 1 1) v3273_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3273_pg : Scalar.QComplex := ((-93086376380946854969705 : Int)/10^30,(99771342505495907480 : Int)/10^30)
theorem v3273_pg_checked : Scalar.distance (sourceCoefficient 43 49 1 2) v3273_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3273_mb : Scalar.QComplex := ((-834808945899849156707894 : Int)/10^30,(-431476712975433725199719872 : Int)/10^30)
theorem v3273_mb_checked : Scalar.distance (sourceCoefficient 43 49 3 1) v3273_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3273_mg : Scalar.QComplex := ((-93086255622459622993634 : Int)/10^30,(180100655718061491303 : Int)/10^30)
theorem v3273_mg_checked : Scalar.distance (sourceCoefficient 43 49 3 2) v3273_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3273_upper : Scalar.QComplex := ((999996086371689983231273684257 : Int)/10^30,(-2797720733659274379135756696 : Int)/10^30)
theorem v3273_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 49 5) 1) 14) v3273_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3273 : Material (43 : Basis) (49 : Basis) where
  plus := ![v3273_pa,v3273_pb,v3273_pg]
  minus := ![(Primitive.Addresses.material3273 1).one,v3273_mb,v3273_mg]
  upper := v3273_upper
  lower := (Primitive.Addresses.material3273 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3273_pa_checked.trans (by decide +kernel)
    · exact v3273_pb_checked.trans (by decide +kernel)
    · exact v3273_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 49 Primitive.Addresses.material3273
    · exact v3273_mb_checked.trans (by decide +kernel)
    · exact v3273_mg_checked.trans (by decide +kernel)
  upper_error := v3273_upper_checked
  lower_error := reuse_lower_error 43 49 Primitive.Addresses.material3273

def v3274_pa : Scalar.QComplex := ((999999422843627701859830402991 : Int)/10^30,(-1074389320259095955448210236 : Int)/10^30)
theorem v3274_pa_checked : Scalar.distance (sourceCoefficient 43 50 1 0) v3274_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3274_pb : Scalar.QComplex := ((-463574839986603717323919 : Int)/10^30,(-431477271497483580767611995 : Int)/10^30)
theorem v3274_pb_checked : Scalar.distance (sourceCoefficient 43 50 1 1) v3274_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3274_pg : Scalar.QComplex := ((-93086376120509482808105 : Int)/10^30,(100011066087520817591 : Int)/10^30)
theorem v3274_pg_checked : Scalar.distance (sourceCoefficient 43 50 1 2) v3274_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3274_mb : Scalar.QComplex := ((-835920119663911880008182 : Int)/10^30,(-431476710794567644087291141 : Int)/10^30)
theorem v3274_mb_checked : Scalar.distance (sourceCoefficient 43 50 3 1) v3274_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3274_mg : Scalar.QComplex := ((-93086255155151693266612 : Int)/10^30,(180340378986080633406 : Int)/10^30)
theorem v3274_mg_checked : Scalar.distance (sourceCoefficient 43 50 3 2) v3274_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3274_upper : Scalar.QComplex := ((999996079163456630730761006381 : Int)/10^30,(-2800296004671530908926151973 : Int)/10^30)
theorem v3274_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 50 5) 1) 14) v3274_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3274 : Material (43 : Basis) (50 : Basis) where
  plus := ![v3274_pa,v3274_pb,v3274_pg]
  minus := ![(Primitive.Addresses.material3274 1).one,v3274_mb,v3274_mg]
  upper := v3274_upper
  lower := (Primitive.Addresses.material3274 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3274_pa_checked.trans (by decide +kernel)
    · exact v3274_pb_checked.trans (by decide +kernel)
    · exact v3274_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 50 Primitive.Addresses.material3274
    · exact v3274_mb_checked.trans (by decide +kernel)
    · exact v3274_mg_checked.trans (by decide +kernel)
  upper_error := v3274_upper_checked
  lower_error := reuse_lower_error 43 50 Primitive.Addresses.material3274

def v3275_pa : Scalar.QComplex := ((999999410639997131707668915161 : Int)/10^30,(-1085688564180065259130661144 : Int)/10^30)
theorem v3275_pa_checked : Scalar.distance (sourceCoefficient 43 51 1 0) v3275_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3275_pb : Scalar.QComplex := ((-468450209584372038771384 : Int)/10^30,(-431477266090887099687724656 : Int)/10^30)
theorem v3275_pb_checked : Scalar.distance (sourceCoefficient 43 51 1 1) v3275_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3275_pg : Scalar.QComplex := ((-93086374969307043346231 : Int)/10^30,(101062872347568866837 : Int)/10^30)
theorem v3275_pg_checked : Scalar.distance (sourceCoefficient 43 51 1 2) v3275_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3275_mb : Scalar.QComplex := ((-840795482780708025702849 : Int)/10^30,(-431476701180748791751852548 : Int)/10^30)
theorem v3275_mb_checked : Scalar.distance (sourceCoefficient 43 51 3 1) v3275_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3275_mg : Scalar.QComplex := ((-93086253096288251623989 : Int)/10^30,(181392183861057285093 : Int)/10^30)
theorem v3275_mg_checked : Scalar.distance (sourceCoefficient 43 51 3 2) v3275_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3275_upper : Scalar.QComplex := ((999996047458374288260962179142 : Int)/10^30,(-2811595210701244435388158421 : Int)/10^30)
theorem v3275_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 51 5) 1) 14) v3275_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3275 : Material (43 : Basis) (51 : Basis) where
  plus := ![v3275_pa,v3275_pb,v3275_pg]
  minus := ![(Primitive.Addresses.material3275 1).one,v3275_mb,v3275_mg]
  upper := v3275_upper
  lower := (Primitive.Addresses.material3275 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3275_pa_checked.trans (by decide +kernel)
    · exact v3275_pb_checked.trans (by decide +kernel)
    · exact v3275_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 51 Primitive.Addresses.material3275
    · exact v3275_mb_checked.trans (by decide +kernel)
    · exact v3275_mg_checked.trans (by decide +kernel)
  upper_error := v3275_upper_checked
  lower_error := reuse_lower_error 43 51 Primitive.Addresses.material3275

def v3276_pa : Scalar.QComplex := ((999999384085798114454931026674 : Int)/10^30,(-1109877481716241530863928166 : Int)/10^30)
theorem v3276_pa_checked : Scalar.distance (sourceCoefficient 43 52 1 0) v3276_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3276_pb : Scalar.QComplex := ((-478887183340177043754000 : Int)/10^30,(-431477254269760064121009147 : Int)/10^30)
theorem v3276_pb_checked : Scalar.distance (sourceCoefficient 43 52 1 1) v3276_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3276_pg : Scalar.QComplex := ((-93086372458251544517883 : Int)/10^30,(103314532278952019575 : Int)/10^30)
theorem v3276_pg_checked : Scalar.distance (sourceCoefficient 43 52 1 2) v3276_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3276_mb : Scalar.QComplex := ((-851232442449250480238525 : Int)/10^30,(-431476680352987870319636456 : Int)/10^30)
theorem v3276_mb_checked : Scalar.distance (sourceCoefficient 43 52 3 1) v3276_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3276_mg : Scalar.QComplex := ((-93086248642152577991459 : Int)/10^30,(183643840787116737687 : Int)/10^30)
theorem v3276_mg_checked : Scalar.distance (sourceCoefficient 43 52 3 2) v3276_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3276_upper : Scalar.QComplex := ((999995979156337554385298581538 : Int)/10^30,(-2835784046380730941178943923 : Int)/10^30)
theorem v3276_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 52 5) 1) 14) v3276_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3276 : Material (43 : Basis) (52 : Basis) where
  plus := ![v3276_pa,v3276_pb,v3276_pg]
  minus := ![(Primitive.Addresses.material3276 1).one,v3276_mb,v3276_mg]
  upper := v3276_upper
  lower := (Primitive.Addresses.material3276 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3276_pa_checked.trans (by decide +kernel)
    · exact v3276_pb_checked.trans (by decide +kernel)
    · exact v3276_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 52 Primitive.Addresses.material3276
    · exact v3276_mb_checked.trans (by decide +kernel)
    · exact v3276_mg_checked.trans (by decide +kernel)
  upper_error := v3276_upper_checked
  lower_error := reuse_lower_error 43 52 Primitive.Addresses.material3276

def v3277_pa : Scalar.QComplex := ((999999379969411045410354267414 : Int)/10^30,(-1113580169305851123232566909 : Int)/10^30)
theorem v3277_pa_checked : Scalar.distance (sourceCoefficient 43 53 1 0) v3277_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3277_pb : Scalar.QComplex := ((-480484809728514022234558 : Int)/10^30,(-431477252430549219150901167 : Int)/10^30)
theorem v3277_pb_checked : Scalar.distance (sourceCoefficient 43 53 1 1) v3277_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3277_pg : Scalar.QComplex := ((-93086372068267113182099 : Int)/10^30,(103659202239724558149 : Int)/10^30)
theorem v3277_pg_checked : Scalar.distance (sourceCoefficient 43 53 1 2) v3277_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3277_mb : Scalar.QComplex := ((-852830066655562014980532 : Int)/10^30,(-431476677135098091458426736 : Int)/10^30)
theorem v3277_mb_checked : Scalar.distance (sourceCoefficient 43 53 3 1) v3277_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3277_mg : Scalar.QComplex := ((-93086247954733639076780 : Int)/10^30,(183988510283013897673 : Int)/10^30)
theorem v3277_mg_checked : Scalar.distance (sourceCoefficient 43 53 3 2) v3277_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3277_upper : Scalar.QComplex := ((999995968649453741743741946886 : Int)/10^30,(-2839486721351111671608662142 : Int)/10^30)
theorem v3277_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 53 5) 1) 14) v3277_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3277 : Material (43 : Basis) (53 : Basis) where
  plus := ![v3277_pa,v3277_pb,v3277_pg]
  minus := ![(Primitive.Addresses.material3277 1).one,v3277_mb,v3277_mg]
  upper := v3277_upper
  lower := (Primitive.Addresses.material3277 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3277_pa_checked.trans (by decide +kernel)
    · exact v3277_pb_checked.trans (by decide +kernel)
    · exact v3277_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 53 Primitive.Addresses.material3277
    · exact v3277_mb_checked.trans (by decide +kernel)
    · exact v3277_mg_checked.trans (by decide +kernel)
  upper_error := v3277_upper_checked
  lower_error := reuse_lower_error 43 53 Primitive.Addresses.material3277

def v3278_pa : Scalar.QComplex := ((999999377871357936665668007241 : Int)/10^30,(-1115462638138374130106006402 : Int)/10^30)
theorem v3278_pa_checked : Scalar.distance (sourceCoefficient 43 54 1 0) v3278_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3278_pb : Scalar.QComplex := ((-481297052675154771615601 : Int)/10^30,(-431477251492458927522293931 : Int)/10^30)
theorem v3278_pb_checked : Scalar.distance (sourceCoefficient 43 54 1 1) v3278_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3278_pg : Scalar.QComplex := ((-93086371869425753313241 : Int)/10^30,(103834434538575146966 : Int)/10^30)
theorem v3278_pg_checked : Scalar.distance (sourceCoefficient 43 54 1 2) v3278_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3278_mb : Scalar.QComplex := ((-853642308490237922333584 : Int)/10^30,(-431476675496079068237067840 : Int)/10^30)
theorem v3278_mb_checked : Scalar.distance (sourceCoefficient 43 54 3 1) v3278_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3278_mg : Scalar.QComplex := ((-93086247604674771507360 : Int)/10^30,(184163742345026355033 : Int)/10^30)
theorem v3278_mg_checked : Scalar.distance (sourceCoefficient 43 54 3 2) v3278_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3278_upper : Scalar.QComplex := ((999995963302433329106452389550 : Int)/10^30,(-2841369183758869150959599058 : Int)/10^30)
theorem v3278_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 54 5) 1) 14) v3278_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3278 : Material (43 : Basis) (54 : Basis) where
  plus := ![v3278_pa,v3278_pb,v3278_pg]
  minus := ![(Primitive.Addresses.material3278 1).one,v3278_mb,v3278_mg]
  upper := v3278_upper
  lower := (Primitive.Addresses.material3278 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3278_pa_checked.trans (by decide +kernel)
    · exact v3278_pb_checked.trans (by decide +kernel)
    · exact v3278_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 54 Primitive.Addresses.material3278
    · exact v3278_mb_checked.trans (by decide +kernel)
    · exact v3278_mg_checked.trans (by decide +kernel)
  upper_error := v3278_upper_checked
  lower_error := reuse_lower_error 43 54 Primitive.Addresses.material3278

def v3279_pa : Scalar.QComplex := ((999999360638436934602295417293 : Int)/10^30,(-1130806224490998759967830166 : Int)/10^30)
theorem v3279_pa_checked : Scalar.distance (sourceCoefficient 43 55 1 0) v3279_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3279_pb : Scalar.QComplex := ((-487917464937307166635293 : Int)/10^30,(-431477243770263636050403925 : Int)/10^30)
theorem v3279_pb_checked : Scalar.distance (sourceCoefficient 43 55 1 1) v3279_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3279_pg : Scalar.QComplex := ((-93086370234361748162450 : Int)/10^30,(105262714177223364700 : Int)/10^30)
theorem v3279_pg_checked : Scalar.distance (sourceCoefficient 43 55 1 2) v3279_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3279_mb : Scalar.QComplex := ((-860262711623401522591346 : Int)/10^30,(-431476662060769042153501001 : Int)/10^30)
theorem v3279_mb_checked : Scalar.distance (sourceCoefficient 43 55 3 1) v3279_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3279_mg : Scalar.QComplex := ((-93086244737070374339194 : Int)/10^30,(185592020040874191798 : Int)/10^30)
theorem v3279_mg_checked : Scalar.distance (sourceCoefficient 43 55 3 2) v3279_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3279_upper : Scalar.QComplex := ((999995919587899908105001050880 : Int)/10^30,(-2856712717516566001670245536 : Int)/10^30)
theorem v3279_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 55 5) 1) 14) v3279_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3279 : Material (43 : Basis) (55 : Basis) where
  plus := ![v3279_pa,v3279_pb,v3279_pg]
  minus := ![(Primitive.Addresses.material3279 1).one,v3279_mb,v3279_mg]
  upper := v3279_upper
  lower := (Primitive.Addresses.material3279 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3279_pa_checked.trans (by decide +kernel)
    · exact v3279_pb_checked.trans (by decide +kernel)
    · exact v3279_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 55 Primitive.Addresses.material3279
    · exact v3279_mb_checked.trans (by decide +kernel)
    · exact v3279_mg_checked.trans (by decide +kernel)
  upper_error := v3279_upper_checked
  lower_error := reuse_lower_error 43 55 Primitive.Addresses.material3279

def v3280_pa : Scalar.QComplex := ((999999356514016736913025893837 : Int)/10^30,(-1134447686079866484096340029 : Int)/10^30)
theorem v3280_pa_checked : Scalar.distance (sourceCoefficient 43 56 1 0) v3280_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3280_pb : Scalar.QComplex := ((-489488673668740612431313 : Int)/10^30,(-431477241917684664639439670 : Int)/10^30)
theorem v3280_pb_checked : Scalar.distance (sourceCoefficient 43 56 1 1) v3280_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3280_pg : Scalar.QComplex := ((-93086369842561417620079 : Int)/10^30,(105601684826672460539 : Int)/10^30)
theorem v3280_pg_checked : Scalar.distance (sourceCoefficient 43 56 1 2) v3280_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3280_mb : Scalar.QComplex := ((-861833918171109934620172 : Int)/10^30,(-431476658852308389929648921 : Int)/10^30)
theorem v3280_mb_checked : Scalar.distance (sourceCoefficient 43 56 3 1) v3280_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3280_mg : Scalar.QComplex := ((-93086244052753785878748 : Int)/10^30,(185930990226002983896 : Int)/10^30)
theorem v3280_mg_checked : Scalar.distance (sourceCoefficient 43 56 3 2) v3280_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3280_upper : Scalar.QComplex := ((999995909178653501684218841678 : Int)/10^30,(-2860354166563529348572580394 : Int)/10^30)
theorem v3280_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 56 5) 1) 14) v3280_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3280 : Material (43 : Basis) (56 : Basis) where
  plus := ![v3280_pa,v3280_pb,v3280_pg]
  minus := ![(Primitive.Addresses.material3280 1).one,v3280_mb,v3280_mg]
  upper := v3280_upper
  lower := (Primitive.Addresses.material3280 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3280_pa_checked.trans (by decide +kernel)
    · exact v3280_pb_checked.trans (by decide +kernel)
    · exact v3280_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 56 Primitive.Addresses.material3280
    · exact v3280_mb_checked.trans (by decide +kernel)
    · exact v3280_mg_checked.trans (by decide +kernel)
  upper_error := v3280_upper_checked
  lower_error := reuse_lower_error 43 56 Primitive.Addresses.material3280

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
