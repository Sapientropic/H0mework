import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B053
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B054

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1281_pa : Scalar.QComplex := ((999999953310551856958748716645 : Int)/10^30,(-305579603550659013327121870 : Int)/10^30)
theorem v1281_pa_checked : Scalar.distance (sourceCoefficient 14 29 1 0) v1281_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1281_pb : Scalar.QComplex := ((-131850728449504224779764 : Int)/10^30,(-431477496408258321382118902 : Int)/10^30)
theorem v1281_pb_checked : Scalar.distance (sourceCoefficient 14 29 1 1) v1281_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1281_pg : Scalar.QComplex := ((-93086425071132572361996 : Int)/10^30,(28445314197280839333 : Int)/10^30)
theorem v1281_pg_checked : Scalar.distance (sourceCoefficient 14 29 1 2) v1281_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1281_mb : Scalar.QComplex := ((-504196325730728649453952 : Int)/10^30,(-431477221968226597284645446 : Int)/10^30)
theorem v1281_mb_checked : Scalar.distance (sourceCoefficient 14 29 3 1) v1281_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1281_mg : Scalar.QComplex := ((-93086365863777235729214 : Int)/10^30,(108774695985223872384 : Int)/10^30)
theorem v1281_mg_checked : Scalar.distance (sourceCoefficient 14 29 3 2) v1281_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1281_upper : Scalar.QComplex := ((999997936525415883746403388980 : Int)/10^30,(-2031488348552643778976497621 : Int)/10^30)
theorem v1281_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 29 5) 1) 14) v1281_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1281 : Material (14 : Basis) (29 : Basis) where
  plus := ![v1281_pa,v1281_pb,v1281_pg]
  minus := ![(Primitive.Addresses.material1281 1).one,v1281_mb,v1281_mg]
  upper := v1281_upper
  lower := (Primitive.Addresses.material1281 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1281_pa_checked.trans (by decide +kernel)
    · exact v1281_pb_checked.trans (by decide +kernel)
    · exact v1281_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 29 Primitive.Addresses.material1281
    · exact v1281_mb_checked.trans (by decide +kernel)
    · exact v1281_mg_checked.trans (by decide +kernel)
  upper_error := v1281_upper_checked
  lower_error := reuse_lower_error 14 29 Primitive.Addresses.material1281

def v1282_pa : Scalar.QComplex := ((999999951702952820737158068207 : Int)/10^30,(-310795900915570180928024935 : Int)/10^30)
theorem v1282_pa_checked : Scalar.distance (sourceCoefficient 14 30 1 0) v1282_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1282_pb : Scalar.QComplex := ((-134101443423530400504727 : Int)/10^30,(-431477495526095202755360485 : Int)/10^30)
theorem v1282_pb_checked : Scalar.distance (sourceCoefficient 14 30 1 1) v1282_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1282_pg : Scalar.QComplex := ((-93086424901151351699846 : Int)/10^30,(28930880687439009775 : Int)/10^30)
theorem v1282_pg_checked : Scalar.distance (sourceCoefficient 14 30 1 2) v1282_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1282_mb : Scalar.QComplex := ((-506447039105443737370215 : Int)/10^30,(-431477219143798152982400076 : Int)/10^30)
theorem v1282_mb_checked : Scalar.distance (sourceCoefficient 14 30 3 1) v1282_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1282_mg : Scalar.QComplex := ((-93086365274774066455237 : Int)/10^30,(109260262147897309294 : Int)/10^30)
theorem v1282_mg_checked : Scalar.distance (sourceCoefficient 14 30 3 2) v1282_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1282_upper : Scalar.QComplex := ((999997925914963208818422400422 : Int)/10^30,(-2036704635373922674600851009 : Int)/10^30)
theorem v1282_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 30 5) 1) 14) v1282_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1282 : Material (14 : Basis) (30 : Basis) where
  plus := ![v1282_pa,v1282_pb,v1282_pg]
  minus := ![(Primitive.Addresses.material1282 1).one,v1282_mb,v1282_mg]
  upper := v1282_upper
  lower := (Primitive.Addresses.material1282 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1282_pa_checked.trans (by decide +kernel)
    · exact v1282_pb_checked.trans (by decide +kernel)
    · exact v1282_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 30 Primitive.Addresses.material1282
    · exact v1282_mb_checked.trans (by decide +kernel)
    · exact v1282_mg_checked.trans (by decide +kernel)
  upper_error := v1282_upper_checked
  lower_error := reuse_lower_error 14 30 Primitive.Addresses.material1282

def v1283_pa : Scalar.QComplex := ((999999948193100422912463378271 : Int)/10^30,(-321890969848829759701201026 : Int)/10^30)
theorem v1283_pa_checked : Scalar.distance (sourceCoefficient 14 31 1 0) v1283_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1283_pb : Scalar.QComplex := ((-138888716077491772763346 : Int)/10^30,(-431477493597675520182473708 : Int)/10^30)
theorem v1283_pb_checked : Scalar.distance (sourceCoefficient 14 31 1 1) v1283_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1283_pg : Scalar.QComplex := ((-93086424529774091722735 : Int)/10^30,(29963681023974292870 : Int)/10^30)
theorem v1283_pg_checked : Scalar.distance (sourceCoefficient 14 31 1 2) v1283_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1283_mb : Scalar.QComplex := ((-511234308312745378128299 : Int)/10^30,(-431477213084178498836116911 : Int)/10^30)
theorem v1283_mb_checked : Scalar.distance (sourceCoefficient 14 31 3 1) v1283_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1283_mg : Scalar.QComplex := ((-93086364012136769929320 : Int)/10^30,(110293061779391976640 : Int)/10^30)
theorem v1283_mg_checked : Scalar.distance (sourceCoefficient 14 31 3 2) v1283_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1283_upper : Scalar.QComplex := ((999997903256033596491536469450 : Int)/10^30,(-2047799681724693568310720704 : Int)/10^30)
theorem v1283_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 31 5) 1) 14) v1283_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1283 : Material (14 : Basis) (31 : Basis) where
  plus := ![v1283_pa,v1283_pb,v1283_pg]
  minus := ![(Primitive.Addresses.material1283 1).one,v1283_mb,v1283_mg]
  upper := v1283_upper
  lower := (Primitive.Addresses.material1283 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1283_pa_checked.trans (by decide +kernel)
    · exact v1283_pb_checked.trans (by decide +kernel)
    · exact v1283_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 31 Primitive.Addresses.material1283
    · exact v1283_mb_checked.trans (by decide +kernel)
    · exact v1283_mg_checked.trans (by decide +kernel)
  upper_error := v1283_upper_checked
  lower_error := reuse_lower_error 14 31 Primitive.Addresses.material1283

def v1284_pa : Scalar.QComplex := ((999999946644314641622565252411 : Int)/10^30,(-326667059664615877279641256 : Int)/10^30)
theorem v1284_pa_checked : Scalar.distance (sourceCoefficient 14 32 1 0) v1284_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1284_pb : Scalar.QComplex := ((-140949491387169822667374 : Int)/10^30,(-431477492745744885230613447 : Int)/10^30)
theorem v1284_pb_checked : Scalar.distance (sourceCoefficient 14 32 1 1) v1284_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1284_pg : Scalar.QComplex := ((-93086424365791388446626 : Int)/10^30,(30408270164719823865 : Int)/10^30)
theorem v1284_pg_checked : Scalar.distance (sourceCoefficient 14 32 1 2) v1284_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1284_mb : Scalar.QComplex := ((-513295082119924829722846 : Int)/10^30,(-431477210453891902719345052 : Int)/10^30)
theorem v1284_mb_checked : Scalar.distance (sourceCoefficient 14 32 3 1) v1284_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1284_mg : Scalar.QComplex := ((-93086363464493722799663 : Int)/10^30,(110737650613086964388 : Int)/10^30)
theorem v1284_mg_checked : Scalar.distance (sourceCoefficient 14 32 3 2) v1284_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1284_upper : Scalar.QComplex := ((999997893464152383372750763065 : Int)/10^30,(-2052575761753991190438487277 : Int)/10^30)
theorem v1284_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 32 5) 1) 14) v1284_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1284 : Material (14 : Basis) (32 : Basis) where
  plus := ![v1284_pa,v1284_pb,v1284_pg]
  minus := ![(Primitive.Addresses.material1284 1).one,v1284_mb,v1284_mg]
  upper := v1284_upper
  lower := (Primitive.Addresses.material1284 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1284_pa_checked.trans (by decide +kernel)
    · exact v1284_pb_checked.trans (by decide +kernel)
    · exact v1284_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 32 Primitive.Addresses.material1284
    · exact v1284_mb_checked.trans (by decide +kernel)
    · exact v1284_mg_checked.trans (by decide +kernel)
  upper_error := v1284_upper_checked
  lower_error := reuse_lower_error 14 32 Primitive.Addresses.material1284

def v1285_pa : Scalar.QComplex := ((999999944447828330418378214047 : Int)/10^30,(-333323176891615903675206910 : Int)/10^30)
theorem v1285_pa_checked : Scalar.distance (sourceCoefficient 14 33 1 0) v1285_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1285_pb : Scalar.QComplex := ((-143821456225791547480072 : Int)/10^30,(-431477491536577486360517529 : Int)/10^30)
theorem v1285_pb_checked : Scalar.distance (sourceCoefficient 14 33 1 1) v1285_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1285_pg : Scalar.QComplex := ((-93086424133127710119683 : Int)/10^30,(31027864341199757747 : Int)/10^30)
theorem v1285_pg_checked : Scalar.distance (sourceCoefficient 14 33 1 2) v1285_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1285_mb : Scalar.QComplex := ((-516167044845725783492552 : Int)/10^30,(-431477206766348646841674596 : Int)/10^30)
theorem v1285_mb_checked : Scalar.distance (sourceCoefficient 14 33 3 1) v1285_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1285_mg : Scalar.QComplex := ((-93086362697148262287666 : Int)/10^30,(111357244358085393900 : Int)/10^30)
theorem v1285_mg_checked : Scalar.distance (sourceCoefficient 14 33 3 2) v1285_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1285_upper : Scalar.QComplex := ((999997879779814848012769282881 : Int)/10^30,(-2059231865276550380214406918 : Int)/10^30)
theorem v1285_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 33 5) 1) 14) v1285_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1285 : Material (14 : Basis) (33 : Basis) where
  plus := ![v1285_pa,v1285_pb,v1285_pg]
  minus := ![(Primitive.Addresses.material1285 1).one,v1285_mb,v1285_mg]
  upper := v1285_upper
  lower := (Primitive.Addresses.material1285 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1285_pa_checked.trans (by decide +kernel)
    · exact v1285_pb_checked.trans (by decide +kernel)
    · exact v1285_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 33 Primitive.Addresses.material1285
    · exact v1285_mb_checked.trans (by decide +kernel)
    · exact v1285_mg_checked.trans (by decide +kernel)
  upper_error := v1285_upper_checked
  lower_error := reuse_lower_error 14 33 Primitive.Addresses.material1285

def v1286_pa : Scalar.QComplex := ((999999938928318746879853090702 : Int)/10^30,(-349490141172093784050795696 : Int)/10^30)
theorem v1286_pa_checked : Scalar.distance (sourceCoefficient 14 34 1 0) v1286_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1286_pb : Scalar.QComplex := ((-150797137575611093716817 : Int)/10^30,(-431477488493507403656939807 : Int)/10^30)
theorem v1286_pb_checked : Scalar.distance (sourceCoefficient 14 34 1 1) v1286_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1286_pg : Scalar.QComplex := ((-93086423547977890477330 : Int)/10^30,(32532789293820246107 : Int)/10^30)
theorem v1286_pg_checked : Scalar.distance (sourceCoefficient 14 34 1 2) v1286_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1286_mb : Scalar.QComplex := ((-523142720972147932220162 : Int)/10^30,(-431477197703580865343240400 : Int)/10^30)
theorem v1286_mb_checked : Scalar.distance (sourceCoefficient 14 34 3 1) v1286_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1286_mg : Scalar.QComplex := ((-93086360813316205715632 : Int)/10^30,(112862168245395603750 : Int)/10^30)
theorem v1286_mg_checked : Scalar.distance (sourceCoefficient 14 34 3 2) v1286_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1286_upper : Scalar.QComplex := ((999997846357599792573220760495 : Int)/10^30,(-2075398795952061254657897432 : Int)/10^30)
theorem v1286_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 34 5) 1) 14) v1286_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1286 : Material (14 : Basis) (34 : Basis) where
  plus := ![v1286_pa,v1286_pb,v1286_pg]
  minus := ![(Primitive.Addresses.material1286 1).one,v1286_mb,v1286_mg]
  upper := v1286_upper
  lower := (Primitive.Addresses.material1286 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1286_pa_checked.trans (by decide +kernel)
    · exact v1286_pb_checked.trans (by decide +kernel)
    · exact v1286_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 34 Primitive.Addresses.material1286
    · exact v1286_mb_checked.trans (by decide +kernel)
    · exact v1286_mg_checked.trans (by decide +kernel)
  upper_error := v1286_upper_checked
  lower_error := reuse_lower_error 14 34 Primitive.Addresses.material1286

def v1287_pa : Scalar.QComplex := ((999999919658736955666029203365 : Int)/10^30,(-400852241647654247010870713 : Int)/10^30)
theorem v1287_pa_checked : Scalar.distance (sourceCoefficient 14 35 1 0) v1287_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1287_pb : Scalar.QComplex := ((-172958728103567549117019 : Int)/10^30,(-431477477828037532987105030 : Int)/10^30)
theorem v1287_pb_checked : Scalar.distance (sourceCoefficient 14 35 1 1) v1287_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1287_pg : Scalar.QComplex := ((-93086421500631926127419 : Int)/10^30,(37313903723332860975 : Int)/10^30)
theorem v1287_pg_checked : Scalar.distance (sourceCoefficient 14 35 1 2) v1287_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1287_mb : Scalar.QComplex := ((-545304294044511255883291 : Int)/10^30,(-431477167913660461274240053 : Int)/10^30)
theorem v1287_mb_checked : Scalar.distance (sourceCoefficient 14 35 3 1) v1287_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1287_mg : Scalar.QComplex := ((-93086354640084584417159 : Int)/10^30,(117643279127913450592 : Int)/10^30)
theorem v1287_mg_checked : Scalar.distance (sourceCoefficient 14 35 3 2) v1287_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1287_upper : Scalar.QComplex := ((999997738441720813677417473413 : Int)/10^30,(-2126760786672256426586343400 : Int)/10^30)
theorem v1287_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 35 5) 1) 14) v1287_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1287 : Material (14 : Basis) (35 : Basis) where
  plus := ![v1287_pa,v1287_pb,v1287_pg]
  minus := ![(Primitive.Addresses.material1287 1).one,v1287_mb,v1287_mg]
  upper := v1287_upper
  lower := (Primitive.Addresses.material1287 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1287_pa_checked.trans (by decide +kernel)
    · exact v1287_pb_checked.trans (by decide +kernel)
    · exact v1287_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 35 Primitive.Addresses.material1287
    · exact v1287_mb_checked.trans (by decide +kernel)
    · exact v1287_mg_checked.trans (by decide +kernel)
  upper_error := v1287_upper_checked
  lower_error := reuse_lower_error 14 35 Primitive.Addresses.material1287

def v1288_pa : Scalar.QComplex := ((999999913056678567269484369961 : Int)/10^30,(-416997164626235665613315316 : Int)/10^30)
theorem v1288_pa_checked : Scalar.distance (sourceCoefficient 14 36 1 0) v1288_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1288_pb : Scalar.QComplex := ((-179924898968909321301937 : Int)/10^30,(-431477474161993133525249677 : Int)/10^30)
theorem v1288_pb_checked : Scalar.distance (sourceCoefficient 14 36 1 1) v1288_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1288_pg : Scalar.QComplex := ((-93086420797896948164957 : Int)/10^30,(38816776912787193348 : Int)/10^30)
theorem v1288_pg_checked : Scalar.distance (sourceCoefficient 14 36 1 2) v1288_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1288_mb : Scalar.QComplex := ((-552270459152398040940044 : Int)/10^30,(-431477158236125714747336406 : Int)/10^30)
theorem v1288_mb_checked : Scalar.distance (sourceCoefficient 14 36 3 1) v1288_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1288_mg : Scalar.QComplex := ((-93086352640437992511754 : Int)/10^30,(119146151151350773860 : Int)/10^30)
theorem v1288_mg_checked : Scalar.distance (sourceCoefficient 14 36 3 2) v1288_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1288_upper : Scalar.QComplex := ((999997703974999853211133728656 : Int)/10^30,(-2142905674210317740153746124 : Int)/10^30)
theorem v1288_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 36 5) 1) 14) v1288_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1288 : Material (14 : Basis) (36 : Basis) where
  plus := ![v1288_pa,v1288_pb,v1288_pg]
  minus := ![(Primitive.Addresses.material1288 1).one,v1288_mb,v1288_mg]
  upper := v1288_upper
  lower := (Primitive.Addresses.material1288 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1288_pa_checked.trans (by decide +kernel)
    · exact v1288_pb_checked.trans (by decide +kernel)
    · exact v1288_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 36 Primitive.Addresses.material1288
    · exact v1288_mb_checked.trans (by decide +kernel)
    · exact v1288_mg_checked.trans (by decide +kernel)
  upper_error := v1288_upper_checked
  lower_error := reuse_lower_error 14 36 Primitive.Addresses.material1288

def v1289_pa : Scalar.QComplex := ((999999910158112409177553069748 : Int)/10^30,(-423891220845726088951871841 : Int)/10^30)
theorem v1289_pa_checked : Scalar.distance (sourceCoefficient 14 37 1 0) v1289_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1289_pb : Scalar.QComplex := ((-182899529039053079201166 : Int)/10^30,(-431477472550864336206142503 : Int)/10^30)
theorem v1289_pb_checked : Scalar.distance (sourceCoefficient 14 37 1 1) v1289_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1289_pg : Scalar.QComplex := ((-93086420489196887658295 : Int)/10^30,(39458519970352195541 : Int)/10^30)
theorem v1289_pg_checked : Scalar.distance (sourceCoefficient 14 37 1 2) v1289_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1289_mb : Scalar.QComplex := ((-555245086724619486875606 : Int)/10^30,(-431477154058025739156120943 : Int)/10^30)
theorem v1289_mb_checked : Scalar.distance (sourceCoefficient 14 37 3 1) v1289_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1289_mg : Scalar.QComplex := ((-93086351777942691304018 : Int)/10^30,(119787893703571257732 : Int)/10^30)
theorem v1289_mg_checked : Scalar.distance (sourceCoefficient 14 37 3 2) v1289_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1289_upper : Scalar.QComplex := ((999997689177922401247223541670 : Int)/10^30,(-2149799715159259024293595223 : Int)/10^30)
theorem v1289_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 37 5) 1) 14) v1289_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1289 : Material (14 : Basis) (37 : Basis) where
  plus := ![v1289_pa,v1289_pb,v1289_pg]
  minus := ![(Primitive.Addresses.material1289 1).one,v1289_mb,v1289_mg]
  upper := v1289_upper
  lower := (Primitive.Addresses.material1289 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1289_pa_checked.trans (by decide +kernel)
    · exact v1289_pb_checked.trans (by decide +kernel)
    · exact v1289_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 37 Primitive.Addresses.material1289
    · exact v1289_mb_checked.trans (by decide +kernel)
    · exact v1289_mg_checked.trans (by decide +kernel)
  upper_error := v1289_upper_checked
  lower_error := reuse_lower_error 14 37 Primitive.Addresses.material1289

def v1290_pa : Scalar.QComplex := ((999999900009547637439601455832 : Int)/10^30,(-447192234645270012674797626 : Int)/10^30)
theorem v1290_pa_checked : Scalar.distance (sourceCoefficient 14 38 1 0) v1290_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1290_pb : Scalar.QComplex := ((-192953391916962988388451 : Int)/10^30,(-431477466903073668277256159 : Int)/10^30)
theorem v1290_pb_checked : Scalar.distance (sourceCoefficient 14 38 1 1) v1290_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1290_pg : Scalar.QComplex := ((-93086419407626349200679 : Int)/10^30,(41627528072378621460 : Int)/10^30)
theorem v1290_pg_checked : Scalar.distance (sourceCoefficient 14 38 1 2) v1290_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1290_mb : Scalar.QComplex := ((-565298940985227783011036 : Int)/10^30,(-431477139734206319696519795 : Int)/10^30)
theorem v1290_mb_checked : Scalar.distance (sourceCoefficient 14 38 3 1) v1290_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1290_mg : Scalar.QComplex := ((-93086348824616252014286 : Int)/10^30,(121956900064630176139 : Int)/10^30)
theorem v1290_mg_checked : Scalar.distance (sourceCoefficient 14 38 3 2) v1290_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1290_upper : Scalar.QComplex := ((999997638813936778050946128211 : Int)/10^30,(-2173100676739177897534094806 : Int)/10^30)
theorem v1290_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 38 5) 1) 14) v1290_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1290 : Material (14 : Basis) (38 : Basis) where
  plus := ![v1290_pa,v1290_pb,v1290_pg]
  minus := ![(Primitive.Addresses.material1290 1).one,v1290_mb,v1290_mg]
  upper := v1290_upper
  lower := (Primitive.Addresses.material1290 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1290_pa_checked.trans (by decide +kernel)
    · exact v1290_pb_checked.trans (by decide +kernel)
    · exact v1290_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 38 Primitive.Addresses.material1290
    · exact v1290_mb_checked.trans (by decide +kernel)
    · exact v1290_mg_checked.trans (by decide +kernel)
  upper_error := v1290_upper_checked
  lower_error := reuse_lower_error 14 38 Primitive.Addresses.material1290

def v1291_pa : Scalar.QComplex := ((999999893873314188775238246738 : Int)/10^30,(-460709626944755824723689872 : Int)/10^30)
theorem v1291_pa_checked : Scalar.distance (sourceCoefficient 14 39 1 0) v1291_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1291_pb : Scalar.QComplex := ((-198785842333042014067798 : Int)/10^30,(-431477463483514308438462141 : Int)/10^30)
theorem v1291_pb_checked : Scalar.distance (sourceCoefficient 14 39 1 1) v1291_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1291_pg : Scalar.QComplex := ((-93086418753160551120158 : Int)/10^30,(42885813808721207981 : Int)/10^30)
theorem v1291_pg_checked : Scalar.distance (sourceCoefficient 14 39 1 2) v1291_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1291_mb : Scalar.QComplex := ((-571131386278693246327528 : Int)/10^30,(-431477131281506207855216473 : Int)/10^30)
theorem v1291_mb_checked : Scalar.distance (sourceCoefficient 14 39 3 1) v1291_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1291_mg : Scalar.QComplex := ((-93086347084306778243475 : Int)/10^30,(123215184767680968823 : Int)/10^30)
theorem v1291_mg_checked : Scalar.distance (sourceCoefficient 14 39 3 2) v1291_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1291_upper : Scalar.QComplex := ((999997609347919647923151728801 : Int)/10^30,(-2186618038315513486295028372 : Int)/10^30)
theorem v1291_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 39 5) 1) 14) v1291_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1291 : Material (14 : Basis) (39 : Basis) where
  plus := ![v1291_pa,v1291_pb,v1291_pg]
  minus := ![(Primitive.Addresses.material1291 1).one,v1291_mb,v1291_mg]
  upper := v1291_upper
  lower := (Primitive.Addresses.material1291 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1291_pa_checked.trans (by decide +kernel)
    · exact v1291_pb_checked.trans (by decide +kernel)
    · exact v1291_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 39 Primitive.Addresses.material1291
    · exact v1291_mb_checked.trans (by decide +kernel)
    · exact v1291_mg_checked.trans (by decide +kernel)
  upper_error := v1291_upper_checked
  lower_error := reuse_lower_error 14 39 Primitive.Addresses.material1291

def v1292_pa : Scalar.QComplex := ((999999883140399667090783323682 : Int)/10^30,(-483445123059124719292974450 : Int)/10^30)
theorem v1292_pa_checked : Scalar.distance (sourceCoefficient 14 40 1 0) v1292_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1292_pb : Scalar.QComplex := ((-208595696912278036266165 : Int)/10^30,(-431477457494916709247795462 : Int)/10^30)
theorem v1292_pb_checked : Scalar.distance (sourceCoefficient 14 40 1 1) v1292_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1292_pg : Scalar.QComplex := ((-93086417607629862376213 : Int)/10^30,(45002179874390447097 : Int)/10^30)
theorem v1292_pg_checked : Scalar.distance (sourceCoefficient 14 40 1 2) v1292_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1292_mb : Scalar.QComplex := ((-580941232037382064495956 : Int)/10^30,(-431477116827448156061581144 : Int)/10^30)
theorem v1292_mb_checked : Scalar.distance (sourceCoefficient 14 40 3 1) v1292_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1292_mg : Scalar.QComplex := ((-93086344112447918949648 : Int)/10^30,(125331549056789007384 : Int)/10^30)
theorem v1292_mg_checked : Scalar.distance (sourceCoefficient 14 40 3 2) v1292_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1292_upper : Scalar.QComplex := ((999997559375617366349142132245 : Int)/10^30,(-2209353482043994835463857789 : Int)/10^30)
theorem v1292_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 40 5) 1) 14) v1292_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1292 : Material (14 : Basis) (40 : Basis) where
  plus := ![v1292_pa,v1292_pb,v1292_pg]
  minus := ![(Primitive.Addresses.material1292 1).one,v1292_mb,v1292_mg]
  upper := v1292_upper
  lower := (Primitive.Addresses.material1292 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1292_pa_checked.trans (by decide +kernel)
    · exact v1292_pb_checked.trans (by decide +kernel)
    · exact v1292_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 40 Primitive.Addresses.material1292
    · exact v1292_mb_checked.trans (by decide +kernel)
    · exact v1292_mg_checked.trans (by decide +kernel)
  upper_error := v1292_upper_checked
  lower_error := reuse_lower_error 14 40 Primitive.Addresses.material1292

def v1293_pa : Scalar.QComplex := ((999999876033290198645638258419 : Int)/10^30,(-497929115673068052123175307 : Int)/10^30)
theorem v1293_pa_checked : Scalar.distance (sourceCoefficient 14 41 1 0) v1293_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1293_pb : Scalar.QComplex := ((-214845213500085646365006 : Int)/10^30,(-431477453524720527762102814 : Int)/10^30)
theorem v1293_pb_checked : Scalar.distance (sourceCoefficient 14 41 1 1) v1293_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1293_pg : Scalar.QComplex := ((-93086416848579517518601 : Int)/10^30,(46350442968499694073 : Int)/10^30)
theorem v1293_pg_checked : Scalar.distance (sourceCoefficient 14 41 1 2) v1293_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1293_mb : Scalar.QComplex := ((-587190742872108538312279 : Int)/10^30,(-431477107464202105361946053 : Int)/10^30)
theorem v1293_mb_checked : Scalar.distance (sourceCoefficient 14 41 3 1) v1293_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1293_mg : Scalar.QComplex := ((-93086342189907530020485 : Int)/10^30,(126679810993852024501 : Int)/10^30)
theorem v1293_mg_checked : Scalar.distance (sourceCoefficient 14 41 3 2) v1293_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1293_upper : Scalar.QComplex := ((999997527270461208988205763717 : Int)/10^30,(-2223837440819506388513513380 : Int)/10^30)
theorem v1293_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 41 5) 1) 14) v1293_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1293 : Material (14 : Basis) (41 : Basis) where
  plus := ![v1293_pa,v1293_pb,v1293_pg]
  minus := ![(Primitive.Addresses.material1293 1).one,v1293_mb,v1293_mg]
  upper := v1293_upper
  lower := (Primitive.Addresses.material1293 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1293_pa_checked.trans (by decide +kernel)
    · exact v1293_pb_checked.trans (by decide +kernel)
    · exact v1293_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 41 Primitive.Addresses.material1293
    · exact v1293_mb_checked.trans (by decide +kernel)
    · exact v1293_mg_checked.trans (by decide +kernel)
  upper_error := v1293_upper_checked
  lower_error := reuse_lower_error 14 41 Primitive.Addresses.material1293

def v1294_pa : Scalar.QComplex := ((999999870147406884376305357316 : Int)/10^30,(-509612764135231850683549358 : Int)/10^30)
theorem v1294_pa_checked : Scalar.distance (sourceCoefficient 14 42 1 0) v1294_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1294_pb : Scalar.QComplex := ((-219886444628687319234521 : Int)/10^30,(-431477450234179768505719464 : Int)/10^30)
theorem v1294_pb_checked : Scalar.distance (sourceCoefficient 14 42 1 1) v1294_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1294_pg : Scalar.QComplex := ((-93086416219682976566261 : Int)/10^30,(47438032033106793032 : Int)/10^30)
theorem v1294_pg_checked : Scalar.distance (sourceCoefficient 14 42 1 2) v1294_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1294_mb : Scalar.QComplex := ((-592231969284040991575116 : Int)/10^30,(-431477099823307155962620033 : Int)/10^30)
theorem v1294_mb_checked : Scalar.distance (sourceCoefficient 14 42 3 1) v1294_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1294_mg : Scalar.QComplex := ((-93086340622470843672272 : Int)/10^30,(127767399110790619038 : Int)/10^30)
theorem v1294_mg_checked : Scalar.distance (sourceCoefficient 14 42 3 2) v1294_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1294_upper : Scalar.QComplex := ((999997501219669347664699411455 : Int)/10^30,(-2235521061721747623173485013 : Int)/10^30)
theorem v1294_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 42 5) 1) 14) v1294_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1294 : Material (14 : Basis) (42 : Basis) where
  plus := ![v1294_pa,v1294_pb,v1294_pg]
  minus := ![(Primitive.Addresses.material1294 1).one,v1294_mb,v1294_mg]
  upper := v1294_upper
  lower := (Primitive.Addresses.material1294 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1294_pa_checked.trans (by decide +kernel)
    · exact v1294_pb_checked.trans (by decide +kernel)
    · exact v1294_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 42 Primitive.Addresses.material1294
    · exact v1294_mb_checked.trans (by decide +kernel)
    · exact v1294_mg_checked.trans (by decide +kernel)
  upper_error := v1294_upper_checked
  lower_error := reuse_lower_error 14 42 Primitive.Addresses.material1294

def v1295_pa : Scalar.QComplex := ((999999862139947353376013288253 : Int)/10^30,(-525090550560428441703508190 : Int)/10^30)
theorem v1295_pa_checked : Scalar.distance (sourceCoefficient 14 43 1 0) v1295_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1295_pb : Scalar.QComplex := ((-226564760779680275938375 : Int)/10^30,(-431477445754143155742715413 : Int)/10^30)
theorem v1295_pb_checked : Scalar.distance (sourceCoefficient 14 43 1 1) v1295_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1295_pg : Scalar.QComplex := ((-93086415363731271262024 : Int)/10^30,(48878803831472847496 : Int)/10^30)
theorem v1295_pg_checked : Scalar.distance (sourceCoefficient 14 43 1 2) v1295_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1295_mb : Scalar.QComplex := ((-598910279082321807682696 : Int)/10^30,(-431477089580186153209028152 : Int)/10^30)
theorem v1295_mb_checked : Scalar.distance (sourceCoefficient 14 43 3 1) v1295_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1295_mg : Scalar.QComplex := ((-93086338523198285041039 : Int)/10^30,(129208169634043715403 : Int)/10^30)
theorem v1295_mg_checked : Scalar.distance (sourceCoefficient 14 43 3 2) v1295_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1295_upper : Scalar.QComplex := ((999997466498966506761442792547 : Int)/10^30,(-2250998811274450762922172368 : Int)/10^30)
theorem v1295_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 43 5) 1) 14) v1295_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1295 : Material (14 : Basis) (43 : Basis) where
  plus := ![v1295_pa,v1295_pb,v1295_pg]
  minus := ![(Primitive.Addresses.material1295 1).one,v1295_mb,v1295_mg]
  upper := v1295_upper
  lower := (Primitive.Addresses.material1295 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1295_pa_checked.trans (by decide +kernel)
    · exact v1295_pb_checked.trans (by decide +kernel)
    · exact v1295_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 43 Primitive.Addresses.material1295
    · exact v1295_mb_checked.trans (by decide +kernel)
    · exact v1295_mg_checked.trans (by decide +kernel)
  upper_error := v1295_upper_checked
  lower_error := reuse_lower_error 14 43 Primitive.Addresses.material1295

def v1296_pa : Scalar.QComplex := ((999999859047987836940200232670 : Int)/10^30,(-530946329169577992967483220 : Int)/10^30)
theorem v1296_pa_checked : Scalar.distance (sourceCoefficient 14 44 1 0) v1296_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1296_pb : Scalar.QComplex := ((-229091397314513543466281 : Int)/10^30,(-431477444023256527253245227 : Int)/10^30)
theorem v1296_pb_checked : Scalar.distance (sourceCoefficient 14 44 1 1) v1296_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1296_pg : Scalar.QComplex := ((-93086415033111858369762 : Int)/10^30,(49423897323784338810 : Int)/10^30)
theorem v1296_pg_checked : Scalar.distance (sourceCoefficient 14 44 1 2) v1296_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1296_mb : Scalar.QComplex := ((-601436913182695616151515 : Int)/10^30,(-431477085668926635131887216 : Int)/10^30)
theorem v1296_mb_checked : Scalar.distance (sourceCoefficient 14 44 3 1) v1296_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1296_mg : Scalar.QComplex := ((-93086337722187861488228 : Int)/10^30,(129753262638082324745 : Int)/10^30)
theorem v1296_mg_checked : Scalar.distance (sourceCoefficient 14 44 3 2) v1296_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1296_upper : Scalar.QComplex := ((999997453300468948129661633863 : Int)/10^30,(-2256854575825664318941387383 : Int)/10^30)
theorem v1296_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 44 5) 1) 14) v1296_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1296 : Material (14 : Basis) (44 : Basis) where
  plus := ![v1296_pa,v1296_pb,v1296_pg]
  minus := ![(Primitive.Addresses.material1296 1).one,v1296_mb,v1296_mg]
  upper := v1296_upper
  lower := (Primitive.Addresses.material1296 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1296_pa_checked.trans (by decide +kernel)
    · exact v1296_pb_checked.trans (by decide +kernel)
    · exact v1296_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 44 Primitive.Addresses.material1296
    · exact v1296_mb_checked.trans (by decide +kernel)
    · exact v1296_mg_checked.trans (by decide +kernel)
  upper_error := v1296_upper_checked
  lower_error := reuse_lower_error 14 44 Primitive.Addresses.material1296

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
