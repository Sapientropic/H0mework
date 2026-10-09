import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B176

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4225_pa : Scalar.QComplex := ((999998677493823247177449501085 : Int)/10^30,(-1626348856944000668556061129 : Int)/10^30)
theorem v4225_pa_checked : Scalar.distance (sourceCoefficient 65 66 1 0) v4225_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4225_pb : Scalar.QComplex := ((-701732973040265554405959 : Int)/10^30,(-431476950346721766279536963 : Int)/10^30)
theorem v4225_pb_checked : Scalar.distance (sourceCoefficient 65 66 1 1) v4225_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4225_pg : Scalar.QComplex := ((-93086306787198065650857 : Int)/10^30,(151391008856042462315 : Int)/10^30)
theorem v4225_pg_checked : Scalar.distance (sourceCoefficient 65 66 1 2) v4225_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4225_mb : Scalar.QComplex := ((-1074077886901773064309390 : Int)/10^30,(-431476184124182827530827269 : Int)/10^30)
theorem v4225_mb_checked : Scalar.distance (sourceCoefficient 65 66 3 1) v4225_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4225_mg : Scalar.QComplex := ((-93086141483289549555814 : Int)/10^30,(231720242791976309443 : Int)/10^30)
theorem v4225_mg_checked : Scalar.distance (sourceCoefficient 65 66 3 2) v4225_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4225_upper : Scalar.QComplex := ((999994381182675346897933371304 : Int)/10^30,(-3352253432871398568927569506 : Int)/10^30)
theorem v4225_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 65 66 5) 1) 14) v4225_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4225 : Material (65 : Basis) (66 : Basis) where
  plus := ![v4225_pa,v4225_pb,v4225_pg]
  minus := ![(Primitive.Addresses.material4225 1).one,v4225_mb,v4225_mg]
  upper := v4225_upper
  lower := (Primitive.Addresses.material4225 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4225_pa_checked.trans (by decide +kernel)
    · exact v4225_pb_checked.trans (by decide +kernel)
    · exact v4225_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 65 66 Primitive.Addresses.material4225
    · exact v4225_mb_checked.trans (by decide +kernel)
    · exact v4225_mg_checked.trans (by decide +kernel)
  upper_error := v4225_upper_checked
  lower_error := reuse_lower_error 65 66 Primitive.Addresses.material4225

def v4226_pa : Scalar.QComplex := ((999998629053001320031511908952 : Int)/10^30,(-1655865972192273714569577022 : Int)/10^30)
theorem v4226_pa_checked : Scalar.distance (sourceCoefficient 65 67 1 0) v4226_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4226_pb : Scalar.QComplex := ((-714468944526640795914063 : Int)/10^30,(-431476929308276150215971668 : Int)/10^30)
theorem v4226_pb_checked : Scalar.distance (sourceCoefficient 65 67 1 1) v4226_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4226_pg : Scalar.QComplex := ((-93086302263202282894627 : Int)/10^30,(154138651710763240557 : Int)/10^30)
theorem v4226_pg_checked : Scalar.distance (sourceCoefficient 65 67 1 2) v4226_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4226_mb : Scalar.QComplex := ((-1086813835490733028542071 : Int)/10^30,(-431476152095175259162694584 : Int)/10^30)
theorem v4226_mb_checked : Scalar.distance (sourceCoefficient 65 67 3 1) v4226_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4226_mg : Scalar.QComplex := ((-93086134588203416906328 : Int)/10^30,(234467880719619472079 : Int)/10^30)
theorem v4226_mg_checked : Scalar.distance (sourceCoefficient 65 67 3 2) v4226_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4226_upper : Scalar.QComplex := ((999994281798062419924438309006 : Int)/10^30,(-3381770420552931647344925833 : Int)/10^30)
theorem v4226_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 65 67 5) 1) 14) v4226_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4226 : Material (65 : Basis) (67 : Basis) where
  plus := ![v4226_pa,v4226_pb,v4226_pg]
  minus := ![(Primitive.Addresses.material4226 1).one,v4226_mb,v4226_mg]
  upper := v4226_upper
  lower := (Primitive.Addresses.material4226 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4226_pa_checked.trans (by decide +kernel)
    · exact v4226_pb_checked.trans (by decide +kernel)
    · exact v4226_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 65 67 Primitive.Addresses.material4226
    · exact v4226_mb_checked.trans (by decide +kernel)
    · exact v4226_mg_checked.trans (by decide +kernel)
  upper_error := v4226_upper_checked
  lower_error := reuse_lower_error 65 67 Primitive.Addresses.material4226

def v4227_pa : Scalar.QComplex := ((999998546445717939066402553413 : Int)/10^30,(-1705023885844950940820141397 : Int)/10^30)
theorem v4227_pa_checked : Scalar.distance (sourceCoefficient 65 68 1 0) v4227_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4227_pb : Scalar.QComplex := ((-735679478375082567876749 : Int)/10^30,(-431476893158273700432793845 : Int)/10^30)
theorem v4227_pb_checked : Scalar.distance (sourceCoefficient 65 68 1 1) v4227_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4227_pg : Scalar.QComplex := ((-93086294518915194887884 : Int)/10^30,(158714586299814885330 : Int)/10^30)
theorem v4227_pg_checked : Scalar.distance (sourceCoefficient 65 68 1 2) v4227_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4227_mb : Scalar.QComplex := ((-1108024330245699700953416 : Int)/10^30,(-431476097641450845454930460 : Int)/10^30)
theorem v4227_mb_checked : Scalar.distance (sourceCoefficient 65 68 3 1) v4227_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4227_mg : Scalar.QComplex := ((-93086122895093754543409 : Int)/10^30,(239043806921870571599 : Int)/10^30)
theorem v4227_mg_checked : Scalar.distance (sourceCoefficient 65 68 3 2) v4227_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4227_upper : Scalar.QComplex := ((999994114348802679373612514730 : Int)/10^30,(-3430928118417993940768544188 : Int)/10^30)
theorem v4227_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 65 68 5) 1) 14) v4227_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4227 : Material (65 : Basis) (68 : Basis) where
  plus := ![v4227_pa,v4227_pb,v4227_pg]
  minus := ![(Primitive.Addresses.material4227 1).one,v4227_mb,v4227_mg]
  upper := v4227_upper
  lower := (Primitive.Addresses.material4227 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4227_pa_checked.trans (by decide +kernel)
    · exact v4227_pb_checked.trans (by decide +kernel)
    · exact v4227_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 65 68 Primitive.Addresses.material4227
    · exact v4227_mb_checked.trans (by decide +kernel)
    · exact v4227_mg_checked.trans (by decide +kernel)
  upper_error := v4227_upper_checked
  lower_error := reuse_lower_error 65 68 Primitive.Addresses.material4227

def v4228_pa : Scalar.QComplex := ((999998509322820355660544772041 : Int)/10^30,(-1726659241764345637457891905 : Int)/10^30)
theorem v4228_pa_checked : Scalar.distance (sourceCoefficient 65 69 1 0) v4228_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4228_pb : Scalar.QComplex := ((-745014647523400788296146 : Int)/10^30,(-431476876807373340863913220 : Int)/10^30)
theorem v4228_pb_checked : Scalar.distance (sourceCoefficient 65 69 1 1) v4228_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4228_pg : Scalar.QComplex := ((-93086291027334623063418 : Int)/10^30,(160728544278285884061 : Int)/10^30)
theorem v4228_pg_checked : Scalar.distance (sourceCoefficient 65 69 1 2) v4228_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4228_mb : Scalar.QComplex := ((-1117359481808017216054661 : Int)/10^30,(-431476073234726039485861106 : Int)/10^30)
theorem v4228_mb_checked : Scalar.distance (sourceCoefficient 65 69 3 1) v4228_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4228_mg : Scalar.QComplex := ((-93086117665559452673703 : Int)/10^30,(241057761137376193985 : Int)/10^30)
theorem v4228_mg_checked : Scalar.distance (sourceCoefficient 65 69 3 2) v4228_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4228_upper : Scalar.QComplex := ((999994039885298813444588477764 : Int)/10^30,(-3452563378043313996905271748 : Int)/10^30)
theorem v4228_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 65 69 5) 1) 14) v4228_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4228 : Material (65 : Basis) (69 : Basis) where
  plus := ![v4228_pa,v4228_pb,v4228_pg]
  minus := ![(Primitive.Addresses.material4228 1).one,v4228_mb,v4228_mg]
  upper := v4228_upper
  lower := (Primitive.Addresses.material4228 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4228_pa_checked.trans (by decide +kernel)
    · exact v4228_pb_checked.trans (by decide +kernel)
    · exact v4228_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 65 69 Primitive.Addresses.material4228
    · exact v4228_mb_checked.trans (by decide +kernel)
    · exact v4228_mg_checked.trans (by decide +kernel)
  upper_error := v4228_upper_checked
  lower_error := reuse_lower_error 65 69 Primitive.Addresses.material4228

def v4229_pa : Scalar.QComplex := ((999998484647790170596437142826 : Int)/10^30,(-1740891186538230278158215579 : Int)/10^30)
theorem v4229_pa_checked : Scalar.distance (sourceCoefficient 65 70 1 0) v4229_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4229_pb : Scalar.QComplex := ((-751155411313744400698680 : Int)/10^30,(-431476865904758522654030357 : Int)/10^30)
theorem v4229_pb_checked : Scalar.distance (sourceCoefficient 65 70 1 1) v4229_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4229_pg : Scalar.QComplex := ((-93086288702821031257988 : Int)/10^30,(162053345158189061423 : Int)/10^30)
theorem v4229_pg_checked : Scalar.distance (sourceCoefficient 65 70 1 2) v4229_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4229_mb : Scalar.QComplex := ((-1123500233903408269971004 : Int)/10^30,(-431476057032912699485577615 : Int)/10^30)
theorem v4229_mb_checked : Scalar.distance (sourceCoefficient 65 70 3 1) v4229_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4229_mg : Scalar.QComplex := ((-93086114197803233851171 : Int)/10^30,(242382559518044919845 : Int)/10^30)
theorem v4229_mg_checked : Scalar.distance (sourceCoefficient 65 70 3 2) v4229_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4229_upper : Scalar.QComplex := ((999993990647259811158792784582 : Int)/10^30,(-3466795259033525100406752819 : Int)/10^30)
theorem v4229_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 65 70 5) 1) 14) v4229_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4229 : Material (65 : Basis) (70 : Basis) where
  plus := ![v4229_pa,v4229_pb,v4229_pg]
  minus := ![(Primitive.Addresses.material4229 1).one,v4229_mb,v4229_mg]
  upper := v4229_upper
  lower := (Primitive.Addresses.material4229 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4229_pa_checked.trans (by decide +kernel)
    · exact v4229_pb_checked.trans (by decide +kernel)
    · exact v4229_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 65 70 Primitive.Addresses.material4229
    · exact v4229_mb_checked.trans (by decide +kernel)
    · exact v4229_mg_checked.trans (by decide +kernel)
  upper_error := v4229_upper_checked
  lower_error := reuse_lower_error 65 70 Primitive.Addresses.material4229

def v4230_pa : Scalar.QComplex := ((999998442061570001083297335370 : Int)/10^30,(-1765183965717364468106634151 : Int)/10^30)
theorem v4230_pa_checked : Scalar.distance (sourceCoefficient 65 71 1 0) v4230_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4230_pb : Scalar.QComplex := ((-761637198531858251317018 : Int)/10^30,(-431476847025670088133647162 : Int)/10^30)
theorem v4230_pb_checked : Scalar.distance (sourceCoefficient 65 71 1 1) v4230_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4230_pg : Scalar.QComplex := ((-93086284684245768629011 : Int)/10^30,(164314673144976417273 : Int)/10^30)
theorem v4230_pg_checked : Scalar.distance (sourceCoefficient 65 71 1 2) v4230_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4230_mb : Scalar.QComplex := ((-1133982000926870661532592 : Int)/10^30,(-431476029108521007452172358 : Int)/10^30)
theorem v4230_mb_checked : Scalar.distance (sourceCoefficient 65 71 3 1) v4230_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4230_mg : Scalar.QComplex := ((-93086108227805261355742 : Int)/10^30,(244643883194987056683 : Int)/10^30)
theorem v4230_mg_checked : Scalar.distance (sourceCoefficient 65 71 3 2) v4230_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4230_upper : Scalar.QComplex := ((999993906133970029344259752874 : Int)/10^30,(-3491087928531465712468710901 : Int)/10^30)
theorem v4230_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 65 71 5) 1) 14) v4230_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4230 : Material (65 : Basis) (71 : Basis) where
  plus := ![v4230_pa,v4230_pb,v4230_pg]
  minus := ![(Primitive.Addresses.material4230 1).one,v4230_mb,v4230_mg]
  upper := v4230_upper
  lower := (Primitive.Addresses.material4230 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4230_pa_checked.trans (by decide +kernel)
    · exact v4230_pb_checked.trans (by decide +kernel)
    · exact v4230_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 65 71 Primitive.Addresses.material4230
    · exact v4230_mb_checked.trans (by decide +kernel)
    · exact v4230_mg_checked.trans (by decide +kernel)
  upper_error := v4230_upper_checked
  lower_error := reuse_lower_error 65 71 Primitive.Addresses.material4230

def v4231_pa : Scalar.QComplex := ((999998395179191504872991973963 : Int)/10^30,(-1791546550201927250245935806 : Int)/10^30)
theorem v4231_pa_checked : Scalar.distance (sourceCoefficient 65 72 1 0) v4231_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4231_pb : Scalar.QComplex := ((-773012059933940525523503 : Int)/10^30,(-431476826153902948713999107 : Int)/10^30)
theorem v4231_pb_checked : Scalar.distance (sourceCoefficient 65 72 1 1) v4231_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4231_pg : Scalar.QComplex := ((-93086280250764458718867 : Int)/10^30,(166768671888221708802 : Int)/10^30)
theorem v4231_pg_checked : Scalar.distance (sourceCoefficient 65 72 1 2) v4231_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4231_mb : Scalar.QComplex := ((-1145356840082177167073590 : Int)/10^30,(-431475998420768554288218458 : Int)/10^30)
theorem v4231_mb_checked : Scalar.distance (sourceCoefficient 65 72 3 1) v4231_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4231_mg : Scalar.QComplex := ((-93086101676635210813175 : Int)/10^30,(247097877198601768951 : Int)/10^30)
theorem v4231_mg_checked : Scalar.distance (sourceCoefficient 65 72 3 2) v4231_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4231_upper : Scalar.QComplex := ((999993813752232133556496265123 : Int)/10^30,(-3517450392837323523255814689 : Int)/10^30)
theorem v4231_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 65 72 5) 1) 14) v4231_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4231 : Material (65 : Basis) (72 : Basis) where
  plus := ![v4231_pa,v4231_pb,v4231_pg]
  minus := ![(Primitive.Addresses.material4231 1).one,v4231_mb,v4231_mg]
  upper := v4231_upper
  lower := (Primitive.Addresses.material4231 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4231_pa_checked.trans (by decide +kernel)
    · exact v4231_pb_checked.trans (by decide +kernel)
    · exact v4231_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 65 72 Primitive.Addresses.material4231
    · exact v4231_mb_checked.trans (by decide +kernel)
    · exact v4231_mg_checked.trans (by decide +kernel)
  upper_error := v4231_upper_checked
  lower_error := reuse_lower_error 65 72 Primitive.Addresses.material4231

def v4232_pa : Scalar.QComplex := ((999998378205069049031906454700 : Int)/10^30,(-1800996177587042556362576592 : Int)/10^30)
theorem v4232_pa_checked : Scalar.distance (sourceCoefficient 65 73 1 0) v4232_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4232_pb : Scalar.QComplex := ((-777089361250769494351110 : Int)/10^30,(-431476818575105319249090172 : Int)/10^30)
theorem v4232_pb_checked : Scalar.distance (sourceCoefficient 65 73 1 1) v4232_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4232_pg : Scalar.QComplex := ((-93086278643213987536548 : Int)/10^30,(167648303913400214803 : Int)/10^30)
theorem v4232_pg_checked : Scalar.distance (sourceCoefficient 65 73 1 2) v4232_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4232_mb : Scalar.QComplex := ((-1149434133340679495916131 : Int)/10^30,(-431475987323446345167099529 : Int)/10^30)
theorem v4232_mb_checked : Scalar.distance (sourceCoefficient 65 73 3 1) v4232_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4232_mg : Scalar.QComplex := ((-93086099310002517622071 : Int)/10^30,(247977507509009415565 : Int)/10^30)
theorem v4232_mg_checked : Scalar.distance (sourceCoefficient 65 73 3 2) v4232_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4232_upper : Scalar.QComplex := ((999993780468935355467672572270 : Int)/10^30,(-3526899976852533392029897179 : Int)/10^30)
theorem v4232_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 65 73 5) 1) 14) v4232_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4232 : Material (65 : Basis) (73 : Basis) where
  plus := ![v4232_pa,v4232_pb,v4232_pg]
  minus := ![(Primitive.Addresses.material4232 1).one,v4232_mb,v4232_mg]
  upper := v4232_upper
  lower := (Primitive.Addresses.material4232 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4232_pa_checked.trans (by decide +kernel)
    · exact v4232_pb_checked.trans (by decide +kernel)
    · exact v4232_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 65 73 Primitive.Addresses.material4232
    · exact v4232_mb_checked.trans (by decide +kernel)
    · exact v4232_mg_checked.trans (by decide +kernel)
  upper_error := v4232_upper_checked
  lower_error := reuse_lower_error 65 73 Primitive.Addresses.material4232

def v4233_pa : Scalar.QComplex := ((999998358998237122946764342046 : Int)/10^30,(-1811629330980076814267216411 : Int)/10^30)
theorem v4233_pa_checked : Scalar.distance (sourceCoefficient 65 74 1 0) v4233_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4233_pb : Scalar.QComplex := ((-781677327341627236566433 : Int)/10^30,(-431476809985668895398043024 : Int)/10^30)
theorem v4233_pb_checked : Scalar.distance (sourceCoefficient 65 74 1 1) v4233_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4233_pg : Scalar.QComplex := ((-93086276822729054119212 : Int)/10^30,(168638106139216329428 : Int)/10^30)
theorem v4233_pg_checked : Scalar.distance (sourceCoefficient 65 74 1 2) v4233_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4233_mb : Scalar.QComplex := ((-1154022090310931002168727 : Int)/10^30,(-431475974774805017467663722 : Int)/10^30)
theorem v4233_mb_checked : Scalar.distance (sourceCoefficient 65 74 3 1) v4233_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4233_mg : Scalar.QComplex := ((-93086096635363520212568 : Int)/10^30,(248967307795280419380 : Int)/10^30)
theorem v4233_mg_checked : Scalar.distance (sourceCoefficient 65 74 3 2) v4233_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4233_upper : Scalar.QComplex := ((999993742910273911465885563930 : Int)/10^30,(-3537533081259485254707351858 : Int)/10^30)
theorem v4233_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 65 74 5) 1) 14) v4233_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4233 : Material (65 : Basis) (74 : Basis) where
  plus := ![v4233_pa,v4233_pb,v4233_pg]
  minus := ![(Primitive.Addresses.material4233 1).one,v4233_mb,v4233_mg]
  upper := v4233_upper
  lower := (Primitive.Addresses.material4233 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4233_pa_checked.trans (by decide +kernel)
    · exact v4233_pb_checked.trans (by decide +kernel)
    · exact v4233_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 65 74 Primitive.Addresses.material4233
    · exact v4233_mb_checked.trans (by decide +kernel)
    · exact v4233_mg_checked.trans (by decide +kernel)
  upper_error := v4233_upper_checked
  lower_error := reuse_lower_error 65 74 Primitive.Addresses.material4233

def v4234_pa : Scalar.QComplex := ((999998332048971148973772915459 : Int)/10^30,(-1826444435410346067769582333 : Int)/10^30)
theorem v4234_pa_checked : Scalar.distance (sourceCoefficient 65 75 1 0) v4234_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4234_pb : Scalar.QComplex := ((-788069711012370098610026 : Int)/10^30,(-431476797909611743453003889 : Int)/10^30)
theorem v4234_pb_checked : Scalar.distance (sourceCoefficient 65 75 1 1) v4234_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4234_pg : Scalar.QComplex := ((-93086274265786714092420 : Int)/10^30,(170017191226176469522 : Int)/10^30)
theorem v4234_pg_checked : Scalar.distance (sourceCoefficient 65 75 1 2) v4234_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4234_mb : Scalar.QComplex := ((-1160414461180403840524256 : Int)/10^30,(-431475957182413156412610903 : Int)/10^30)
theorem v4234_mb_checked : Scalar.distance (sourceCoefficient 65 75 3 1) v4234_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4234_mg : Scalar.QComplex := ((-93086092888333813892289 : Int)/10^30,(250346390162218075262 : Int)/10^30)
theorem v4234_mg_checked : Scalar.distance (sourceCoefficient 65 75 3 2) v4234_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4234_upper : Scalar.QComplex := ((999993690391521844389186620061 : Int)/10^30,(-3552348117112408510973664704 : Int)/10^30)
theorem v4234_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 65 75 5) 1) 14) v4234_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4234 : Material (65 : Basis) (75 : Basis) where
  plus := ![v4234_pa,v4234_pb,v4234_pg]
  minus := ![(Primitive.Addresses.material4234 1).one,v4234_mb,v4234_mg]
  upper := v4234_upper
  lower := (Primitive.Addresses.material4234 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4234_pa_checked.trans (by decide +kernel)
    · exact v4234_pb_checked.trans (by decide +kernel)
    · exact v4234_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 65 75 Primitive.Addresses.material4234
    · exact v4234_mb_checked.trans (by decide +kernel)
    · exact v4234_mg_checked.trans (by decide +kernel)
  upper_error := v4234_upper_checked
  lower_error := reuse_lower_error 65 75 Primitive.Addresses.material4234

def v4235_pa : Scalar.QComplex := ((999998309268674362843218406154 : Int)/10^30,(-1838874599504245170433164388 : Int)/10^30)
theorem v4235_pa_checked : Scalar.distance (sourceCoefficient 65 76 1 0) v4235_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4235_pb : Scalar.QComplex := ((-793433046622811184584369 : Int)/10^30,(-431476787680144782580176727 : Int)/10^30)
theorem v4235_pb_checked : Scalar.distance (sourceCoefficient 65 76 1 1) v4235_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4235_pg : Scalar.QComplex := ((-93086272102072151798106 : Int)/10^30,(171174270740742802818 : Int)/10^30)
theorem v4235_pg_checked : Scalar.distance (sourceCoefficient 65 76 1 2) v4235_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4235_mb : Scalar.QComplex := ((-1165777785966260693040991 : Int)/10^30,(-431475942324632928296112154 : Int)/10^30)
theorem v4235_mb_checked : Scalar.distance (sourceCoefficient 65 76 3 1) v4235_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4235_mg : Scalar.QComplex := ((-93086089726112549103861 : Int)/10^30,(251503467378762606965 : Int)/10^30)
theorem v4235_mg_checked : Scalar.distance (sourceCoefficient 65 76 3 2) v4235_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4235_upper : Scalar.QComplex := ((999993646157923416442718000392 : Int)/10^30,(-3564778223376312704938531623 : Int)/10^30)
theorem v4235_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 65 76 5) 1) 14) v4235_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4235 : Material (65 : Basis) (76 : Basis) where
  plus := ![v4235_pa,v4235_pb,v4235_pg]
  minus := ![(Primitive.Addresses.material4235 1).one,v4235_mb,v4235_mg]
  upper := v4235_upper
  lower := (Primitive.Addresses.material4235 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4235_pa_checked.trans (by decide +kernel)
    · exact v4235_pb_checked.trans (by decide +kernel)
    · exact v4235_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 65 76 Primitive.Addresses.material4235
    · exact v4235_mb_checked.trans (by decide +kernel)
    · exact v4235_mg_checked.trans (by decide +kernel)
  upper_error := v4235_upper_checked
  lower_error := reuse_lower_error 65 76 Primitive.Addresses.material4235

def v4236_pa : Scalar.QComplex := ((999998303972816452889602071397 : Int)/10^30,(-1841752288063194850530710576 : Int)/10^30)
theorem v4236_pa_checked : Scalar.distance (sourceCoefficient 65 77 1 0) v4236_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4236_pb : Scalar.QComplex := ((-794674704360973564090330 : Int)/10^30,(-431476785299264837759370185 : Int)/10^30)
theorem v4236_pb_checked : Scalar.distance (sourceCoefficient 65 77 1 1) v4236_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4236_pg : Scalar.QComplex := ((-93086271598761842784958 : Int)/10^30,(171442144474829049858 : Int)/10^30)
theorem v4236_pg_checked : Scalar.distance (sourceCoefficient 65 77 1 2) v4236_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4236_mb : Scalar.QComplex := ((-1167019441187504988538889 : Int)/10^30,(-431475938872259164140184757 : Int)/10^30)
theorem v4236_mb_checked : Scalar.distance (sourceCoefficient 65 77 3 1) v4236_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4236_mg : Scalar.QComplex := ((-93086088991639459564837 : Int)/10^30,(251771340578773091946 : Int)/10^30)
theorem v4236_mg_checked : Scalar.distance (sourceCoefficient 65 77 3 2) v4236_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4236_upper : Scalar.QComplex := ((999993635895444003166980048780 : Int)/10^30,(-3567655898509112997421156139 : Int)/10^30)
theorem v4236_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 65 77 5) 1) 14) v4236_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4236 : Material (65 : Basis) (77 : Basis) where
  plus := ![v4236_pa,v4236_pb,v4236_pg]
  minus := ![(Primitive.Addresses.material4236 1).one,v4236_mb,v4236_mg]
  upper := v4236_upper
  lower := (Primitive.Addresses.material4236 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4236_pa_checked.trans (by decide +kernel)
    · exact v4236_pb_checked.trans (by decide +kernel)
    · exact v4236_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 65 77 Primitive.Addresses.material4236
    · exact v4236_mb_checked.trans (by decide +kernel)
    · exact v4236_mg_checked.trans (by decide +kernel)
  upper_error := v4236_upper_checked
  lower_error := reuse_lower_error 65 77 Primitive.Addresses.material4236

def v4237_pa : Scalar.QComplex := ((999998271961620725048739008611 : Int)/10^30,(-1859051847699052818104055862 : Int)/10^30)
theorem v4237_pa_checked : Scalar.distance (sourceCoefficient 65 78 1 0) v4237_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4237_pb : Scalar.QComplex := ((-802139074281797449227884 : Int)/10^30,(-431476770885920602066264115 : Int)/10^30)
theorem v4237_pb_checked : Scalar.distance (sourceCoefficient 65 78 1 1) v4237_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4237_pg : Scalar.QComplex := ((-93086268554099297343317 : Int)/10^30,(173052498592267733370 : Int)/10^30)
theorem v4237_pg_checked : Scalar.distance (sourceCoefficient 65 78 1 2) v4237_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4237_mb : Scalar.QComplex := ((-1174483795890935891119279 : Int)/10^30,(-431475918017505236264391064 : Int)/10^30)
theorem v4237_mb_checked : Scalar.distance (sourceCoefficient 65 78 3 1) v4237_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4237_mg : Scalar.QComplex := ((-93086084557314972097721 : Int)/10^30,(253381691469196690512 : Int)/10^30)
theorem v4237_mg_checked : Scalar.distance (sourceCoefficient 65 78 3 2) v4237_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4237_upper : Scalar.QComplex := ((999993574026825424541657780944 : Int)/10^30,(-3584955377130889243147609077 : Int)/10^30)
theorem v4237_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 65 78 5) 1) 14) v4237_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4237 : Material (65 : Basis) (78 : Basis) where
  plus := ![v4237_pa,v4237_pb,v4237_pg]
  minus := ![(Primitive.Addresses.material4237 1).one,v4237_mb,v4237_mg]
  upper := v4237_upper
  lower := (Primitive.Addresses.material4237 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4237_pa_checked.trans (by decide +kernel)
    · exact v4237_pb_checked.trans (by decide +kernel)
    · exact v4237_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 65 78 Primitive.Addresses.material4237
    · exact v4237_mb_checked.trans (by decide +kernel)
    · exact v4237_mg_checked.trans (by decide +kernel)
  upper_error := v4237_upper_checked
  lower_error := reuse_lower_error 65 78 Primitive.Addresses.material4237

def v4238_pa : Scalar.QComplex := ((999998261577985967564267255124 : Int)/10^30,(-1864628919102611309947468056 : Int)/10^30)
theorem v4238_pa_checked : Scalar.distance (sourceCoefficient 65 79 1 0) v4238_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4238_pb : Scalar.QComplex := ((-804545454821799867835217 : Int)/10^30,(-431476766202613807947655529 : Int)/10^30)
theorem v4238_pb_checked : Scalar.distance (sourceCoefficient 65 79 1 1) v4238_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4238_pg : Scalar.QComplex := ((-93086267565626128120300 : Int)/10^30,(173571648214964181476 : Int)/10^30)
theorem v4238_pg_checked : Scalar.distance (sourceCoefficient 65 79 1 2) v4238_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4238_mb : Scalar.QComplex := ((-1176890171493450022643678 : Int)/10^30,(-431475911257602159289143254 : Int)/10^30)
theorem v4238_mb_checked : Scalar.distance (sourceCoefficient 65 79 3 1) v4238_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4238_mg : Scalar.QComplex := ((-93086083120839428172446 : Int)/10^30,(253900840045582181917 : Int)/10^30)
theorem v4238_mg_checked : Scalar.distance (sourceCoefficient 65 79 3 2) v4238_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4238_upper : Scalar.QComplex := ((999993554017686837684935170731 : Int)/10^30,(-3590532422306843412786531675 : Int)/10^30)
theorem v4238_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 65 79 5) 1) 14) v4238_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4238 : Material (65 : Basis) (79 : Basis) where
  plus := ![v4238_pa,v4238_pb,v4238_pg]
  minus := ![(Primitive.Addresses.material4238 1).one,v4238_mb,v4238_mg]
  upper := v4238_upper
  lower := (Primitive.Addresses.material4238 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4238_pa_checked.trans (by decide +kernel)
    · exact v4238_pb_checked.trans (by decide +kernel)
    · exact v4238_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 65 79 Primitive.Addresses.material4238
    · exact v4238_mb_checked.trans (by decide +kernel)
    · exact v4238_mg_checked.trans (by decide +kernel)
  upper_error := v4238_upper_checked
  lower_error := reuse_lower_error 65 79 Primitive.Addresses.material4238

def v4239_pa : Scalar.QComplex := ((999998245295479566088024973951 : Int)/10^30,(-1873340855765407663428458517 : Int)/10^30)
theorem v4239_pa_checked : Scalar.distance (sourceCoefficient 65 80 1 0) v4239_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4239_pb : Scalar.QComplex := ((-808304459004337353794848 : Int)/10^30,(-431476758851017336180696182 : Int)/10^30)
theorem v4239_pb_checked : Scalar.distance (sourceCoefficient 65 80 1 1) v4239_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4239_pg : Scalar.QComplex := ((-93086266014773740856124 : Int)/10^30,(174382611226078827165 : Int)/10^30)
theorem v4239_pg_checked : Scalar.distance (sourceCoefficient 65 80 1 2) v4239_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4239_mb : Scalar.QComplex := ((-1180649167932241804945676 : Int)/10^30,(-431475900662157114591381925 : Int)/10^30)
theorem v4239_mb_checked : Scalar.distance (sourceCoefficient 65 80 3 1) v4239_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4239_mg : Scalar.QComplex := ((-93086080870163064187722 : Int)/10^30,(254711801416422473317 : Int)/10^30)
theorem v4239_mg_checked : Scalar.distance (sourceCoefficient 65 80 3 2) v4239_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4239_upper : Scalar.QComplex := ((999993522699192347823040207040 : Int)/10^30,(-3599244317892104571494989872 : Int)/10^30)
theorem v4239_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 65 80 5) 1) 14) v4239_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4239 : Material (65 : Basis) (80 : Basis) where
  plus := ![v4239_pa,v4239_pb,v4239_pg]
  minus := ![(Primitive.Addresses.material4239 1).one,v4239_mb,v4239_mg]
  upper := v4239_upper
  lower := (Primitive.Addresses.material4239 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4239_pa_checked.trans (by decide +kernel)
    · exact v4239_pb_checked.trans (by decide +kernel)
    · exact v4239_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 65 80 Primitive.Addresses.material4239
    · exact v4239_mb_checked.trans (by decide +kernel)
    · exact v4239_mg_checked.trans (by decide +kernel)
  upper_error := v4239_upper_checked
  lower_error := reuse_lower_error 65 80 Primitive.Addresses.material4239

def v4240_pa : Scalar.QComplex := ((999998195809679069683750246800 : Int)/10^30,(-1899572948522356263992236447 : Int)/10^30)
theorem v4240_pa_checked : Scalar.distance (sourceCoefficient 65 81 1 0) v4240_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4240_pb : Scalar.QComplex := ((-819623015235512193183923 : Int)/10^30,(-431476736451300904449092831 : Int)/10^30)
theorem v4240_pb_checked : Scalar.distance (sourceCoefficient 65 81 1 1) v4240_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4240_pg : Scalar.QComplex := ((-93086261295301850484819 : Int)/10^30,(176824462860623423193 : Int)/10^30)
theorem v4240_pg_checked : Scalar.distance (sourceCoefficient 65 81 1 2) v4240_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4240_mb : Scalar.QComplex := ((-1191967700619054441087862 : Int)/10^30,(-431475868495044764643180256 : Int)/10^30)
theorem v4240_mb_checked : Scalar.distance (sourceCoefficient 65 81 3 1) v4240_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4240_mg : Scalar.QComplex := ((-93086074043484947394591 : Int)/10^30,(257153648069062423406 : Int)/10^30)
theorem v4240_mg_checked : Scalar.distance (sourceCoefficient 65 81 3 2) v4240_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4240_upper : Scalar.QComplex := ((999993427939253213077579748070 : Int)/10^30,(-3625476286171430108616914824 : Int)/10^30)
theorem v4240_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 65 81 5) 1) 14) v4240_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4240 : Material (65 : Basis) (81 : Basis) where
  plus := ![v4240_pa,v4240_pb,v4240_pg]
  minus := ![(Primitive.Addresses.material4240 1).one,v4240_mb,v4240_mg]
  upper := v4240_upper
  lower := (Primitive.Addresses.material4240 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4240_pa_checked.trans (by decide +kernel)
    · exact v4240_pb_checked.trans (by decide +kernel)
    · exact v4240_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 65 81 Primitive.Addresses.material4240
    · exact v4240_mb_checked.trans (by decide +kernel)
    · exact v4240_mg_checked.trans (by decide +kernel)
  upper_error := v4240_upper_checked
  lower_error := reuse_lower_error 65 81 Primitive.Addresses.material4240

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
