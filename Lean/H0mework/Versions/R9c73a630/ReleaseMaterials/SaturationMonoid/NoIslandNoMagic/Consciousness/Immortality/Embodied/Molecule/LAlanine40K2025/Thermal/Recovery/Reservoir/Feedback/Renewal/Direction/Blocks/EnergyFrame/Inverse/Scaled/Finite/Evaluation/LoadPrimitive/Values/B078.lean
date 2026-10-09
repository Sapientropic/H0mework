import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B052

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1249_pa : Scalar.QComplex := ((999999415606870953423656959456 : Int)/10^30,(-1081104026714276654040720995 : Int)/10^30)
theorem v1249_pa_checked : Scalar.distance (sourceCoefficient 13 80 1 0) v1249_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1249_pb : Scalar.QComplex := ((-466471998559557368699113 : Int)/10^30,(-431477188531284255295434636 : Int)/10^30)
theorem v1249_pb_checked : Scalar.distance (sourceCoefficient 13 80 1 1) v1249_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1249_pg : Scalar.QComplex := ((-93086366834174557354390 : Int)/10^30,(100636104827676602287 : Int)/10^30)
theorem v1249_pg_checked : Scalar.distance (sourceCoefficient 13 80 1 2) v1249_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1249_mb : Scalar.QComplex := ((-838817205562027629008756 : Int)/10^30,(-431476625328281845442226713 : Int)/10^30)
theorem v1249_mb_checked : Scalar.distance (sourceCoefficient 13 80 3 1) v1249_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1249_mg : Scalar.QComplex := ((-93086245329439943485207 : Int)/10^30,(180965409479817129793 : Int)/10^30)
theorem v1249_mg_checked : Scalar.distance (sourceCoefficient 13 80 3 2) v1249_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1249_upper : Scalar.QComplex := ((999996060337736472362958105425 : Int)/10^30,(-2807010688635959472997926028 : Int)/10^30)
theorem v1249_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 80 5) 1) 14) v1249_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1249 : Material (13 : Basis) (80 : Basis) where
  plus := ![v1249_pa,v1249_pb,v1249_pg]
  minus := ![(Primitive.Addresses.material1249 1).one,v1249_mb,v1249_mg]
  upper := v1249_upper
  lower := (Primitive.Addresses.material1249 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1249_pa_checked.trans (by decide +kernel)
    · exact v1249_pb_checked.trans (by decide +kernel)
    · exact v1249_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 80 Primitive.Addresses.material1249
    · exact v1249_mb_checked.trans (by decide +kernel)
    · exact v1249_mg_checked.trans (by decide +kernel)
  upper_error := v1249_upper_checked
  lower_error := reuse_lower_error 13 80 Primitive.Addresses.material1249

def v1250_pa : Scalar.QComplex := ((999999386903137016519430995627 : Int)/10^30,(-1107336150443575890495058766 : Int)/10^30)
theorem v1250_pa_checked : Scalar.distance (sourceCoefficient 13 81 1 0) v1250_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1250_pb : Scalar.QComplex := ((-477790563699980458361325 : Int)/10^30,(-431477172109563857323425426 : Int)/10^30)
theorem v1250_pb_checked : Scalar.distance (sourceCoefficient 13 81 1 1) v1250_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1250_pg : Scalar.QComplex := ((-93086363726809601922611 : Int)/10^30,(103077958864809085814 : Int)/10^30)
theorem v1250_pg_checked : Scalar.distance (sourceCoefficient 13 81 1 2) v1250_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1250_mb : Scalar.QComplex := ((-850135752316826536291572 : Int)/10^30,(-431476599139155615092505560 : Int)/10^30)
theorem v1250_mb_checked : Scalar.distance (sourceCoefficient 13 81 3 1) v1250_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1250_mg : Scalar.QComplex := ((-93086240114866088045376 : Int)/10^30,(183407259926219751038 : Int)/10^30)
theorem v1250_mg_checked : Scalar.distance (sourceCoefficient 13 81 3 2) v1250_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1250_upper : Scalar.QComplex := ((999995986359779489203231213509 : Int)/10^30,(-2833242723755551063678636594 : Int)/10^30)
theorem v1250_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 81 5) 1) 14) v1250_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1250 : Material (13 : Basis) (81 : Basis) where
  plus := ![v1250_pa,v1250_pb,v1250_pg]
  minus := ![(Primitive.Addresses.material1250 1).one,v1250_mb,v1250_mg]
  upper := v1250_upper
  lower := (Primitive.Addresses.material1250 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1250_pa_checked.trans (by decide +kernel)
    · exact v1250_pb_checked.trans (by decide +kernel)
    · exact v1250_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 81 Primitive.Addresses.material1250
    · exact v1250_mb_checked.trans (by decide +kernel)
    · exact v1250_mg_checked.trans (by decide +kernel)
  upper_error := v1250_upper_checked
  lower_error := reuse_lower_error 13 81 Primitive.Addresses.material1250

def v1251_pa : Scalar.QComplex := ((999999375846524644128658538769 : Int)/10^30,(-1117276403198502122608045612 : Int)/10^30)
theorem v1251_pa_checked : Scalar.distance (sourceCoefficient 13 82 1 0) v1251_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1251_pb : Scalar.QComplex := ((-482079556740370509018411 : Int)/10^30,(-431477165783381033451649490 : Int)/10^30)
theorem v1251_pb_checked : Scalar.distance (sourceCoefficient 13 82 1 1) v1251_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1251_pg : Scalar.QComplex := ((-93086362529797858291681 : Int)/10^30,(104003261228121315854 : Int)/10^30)
theorem v1251_pg_checked : Scalar.distance (sourceCoefficient 13 82 1 2) v1251_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1251_mb : Scalar.QComplex := ((-854424738301017605042368 : Int)/10^30,(-431476589111767321966868082 : Int)/10^30)
theorem v1251_mb_checked : Scalar.distance (sourceCoefficient 13 82 3 1) v1251_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1251_mg : Scalar.QComplex := ((-93086238119360524649599 : Int)/10^30,(184332560912032399463 : Int)/10^30)
theorem v1251_mg_checked : Scalar.distance (sourceCoefficient 13 82 3 2) v1251_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1251_upper : Scalar.QComplex := ((999995958147209102020775145748 : Int)/10^30,(-2843182942622928574734093284 : Int)/10^30)
theorem v1251_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 82 5) 1) 14) v1251_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1251 : Material (13 : Basis) (82 : Basis) where
  plus := ![v1251_pa,v1251_pb,v1251_pg]
  minus := ![(Primitive.Addresses.material1251 1).one,v1251_mb,v1251_mg]
  upper := v1251_upper
  lower := (Primitive.Addresses.material1251 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1251_pa_checked.trans (by decide +kernel)
    · exact v1251_pb_checked.trans (by decide +kernel)
    · exact v1251_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 82 Primitive.Addresses.material1251
    · exact v1251_mb_checked.trans (by decide +kernel)
    · exact v1251_mg_checked.trans (by decide +kernel)
  upper_error := v1251_upper_checked
  lower_error := reuse_lower_error 13 82 Primitive.Addresses.material1251

def v1252_pa : Scalar.QComplex := ((999999360594571101855830481850 : Int)/10^30,(-1130845015445081154387236412 : Int)/10^30)
theorem v1252_pa_checked : Scalar.distance (sourceCoefficient 13 83 1 0) v1252_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1252_pb : Scalar.QComplex := ((-487934104323222838643125 : Int)/10^30,(-431477157056279050464464765 : Int)/10^30)
theorem v1252_pb_checked : Scalar.distance (sourceCoefficient 13 83 1 1) v1252_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1252_pg : Scalar.QComplex := ((-93086360878535772910221 : Int)/10^30,(105266314513267164135 : Int)/10^30)
theorem v1252_pg_checked : Scalar.distance (sourceCoefficient 13 83 1 2) v1252_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1252_mb : Scalar.QComplex := ((-860279276172858346293113 : Int)/10^30,(-431476575332457703511945216 : Int)/10^30)
theorem v1252_mb_checked : Scalar.distance (sourceCoefficient 13 83 3 1) v1252_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1252_mg : Scalar.QComplex := ((-93086235378140954835875 : Int)/10^30,(185595612301920975697 : Int)/10^30)
theorem v1252_mg_checked : Scalar.distance (sourceCoefficient 13 83 3 2) v1252_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1252_upper : Scalar.QComplex := ((999995919477084473033193129728 : Int)/10^30,(-2856751508337165378846345229 : Int)/10^30)
theorem v1252_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 83 5) 1) 14) v1252_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1252 : Material (13 : Basis) (83 : Basis) where
  plus := ![v1252_pa,v1252_pb,v1252_pg]
  minus := ![(Primitive.Addresses.material1252 1).one,v1252_mb,v1252_mg]
  upper := v1252_upper
  lower := (Primitive.Addresses.material1252 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1252_pa_checked.trans (by decide +kernel)
    · exact v1252_pb_checked.trans (by decide +kernel)
    · exact v1252_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 83 Primitive.Addresses.material1252
    · exact v1252_mb_checked.trans (by decide +kernel)
    · exact v1252_mg_checked.trans (by decide +kernel)
  upper_error := v1252_upper_checked
  lower_error := reuse_lower_error 13 83 Primitive.Addresses.material1252

def v1253_pa : Scalar.QComplex := ((999999320240367168086784831672 : Int)/10^30,(-1165984049458082424997801125 : Int)/10^30)
theorem v1253_pa_checked : Scalar.distance (sourceCoefficient 13 84 1 0) v1253_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1253_pb : Scalar.QComplex := ((-503095797891099526800256 : Int)/10^30,(-431477133963118719483525671 : Int)/10^30)
theorem v1253_pb_checked : Scalar.distance (sourceCoefficient 13 84 1 1) v1253_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1253_pg : Scalar.QComplex := ((-93086356509276356168445 : Int)/10^30,(108537280691246847005 : Int)/10^30)
theorem v1253_pg_checked : Scalar.distance (sourceCoefficient 13 84 1 2) v1253_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1253_mb : Scalar.QComplex := ((-875440944166986307197851 : Int)/10^30,(-431476539155447279421866596 : Int)/10^30)
theorem v1253_mb_checked : Scalar.distance (sourceCoefficient 13 84 3 1) v1253_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1253_mg : Scalar.QComplex := ((-93086228186186672220522 : Int)/10^30,(188866573491496367458 : Int)/10^30)
theorem v1253_mg_checked : Scalar.distance (sourceCoefficient 13 84 3 2) v1253_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1253_upper : Scalar.QComplex := ((999995818476155723934400088481 : Int)/10^30,(-2891890420367008123081342427 : Int)/10^30)
theorem v1253_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 84 5) 1) 14) v1253_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1253 : Material (13 : Basis) (84 : Basis) where
  plus := ![v1253_pa,v1253_pb,v1253_pg]
  minus := ![(Primitive.Addresses.material1253 1).one,v1253_mb,v1253_mg]
  upper := v1253_upper
  lower := (Primitive.Addresses.material1253 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1253_pa_checked.trans (by decide +kernel)
    · exact v1253_pb_checked.trans (by decide +kernel)
    · exact v1253_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 84 Primitive.Addresses.material1253
    · exact v1253_mb_checked.trans (by decide +kernel)
    · exact v1253_mg_checked.trans (by decide +kernel)
  upper_error := v1253_upper_checked
  lower_error := reuse_lower_error 13 84 Primitive.Addresses.material1253

def v1254_pa : Scalar.QComplex := ((999999224936391055023898516959 : Int)/10^30,(-1245040809438130141227878760 : Int)/10^30)
theorem v1254_pa_checked : Scalar.distance (sourceCoefficient 13 85 1 0) v1254_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1254_pb : Scalar.QComplex := ((-537206988572945010232837 : Int)/10^30,(-431477079410587081153889430 : Int)/10^30)
theorem v1254_pb_checked : Scalar.distance (sourceCoefficient 13 85 1 1) v1254_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1254_pg : Scalar.QComplex := ((-93086346188974803730390 : Int)/10^30,(115896389633833203811 : Int)/10^30)
theorem v1254_pg_checked : Scalar.distance (sourceCoefficient 13 85 1 2) v1254_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1254_mb : Scalar.QComplex := ((-909552075071298692291153 : Int)/10^30,(-431476455166514706058046302 : Int)/10^30)
theorem v1254_mb_checked : Scalar.distance (sourceCoefficient 13 85 3 1) v1254_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1254_mg : Scalar.QComplex := ((-93086211515309387013440 : Int)/10^30,(196225670787994706418 : Int)/10^30)
theorem v1254_mg_checked : Scalar.distance (sourceCoefficient 13 85 3 2) v1254_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1254_upper : Scalar.QComplex := ((999995586727525802627394012193 : Int)/10^30,(-2970946898115281646438143488 : Int)/10^30)
theorem v1254_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 85 5) 1) 14) v1254_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1254 : Material (13 : Basis) (85 : Basis) where
  plus := ![v1254_pa,v1254_pb,v1254_pg]
  minus := ![(Primitive.Addresses.material1254 1).one,v1254_mb,v1254_mg]
  upper := v1254_upper
  lower := (Primitive.Addresses.material1254 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1254_pa_checked.trans (by decide +kernel)
    · exact v1254_pb_checked.trans (by decide +kernel)
    · exact v1254_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 85 Primitive.Addresses.material1254
    · exact v1254_mb_checked.trans (by decide +kernel)
    · exact v1254_mg_checked.trans (by decide +kernel)
  upper_error := v1254_upper_checked
  lower_error := reuse_lower_error 13 85 Primitive.Addresses.material1254

def v1255_pa : Scalar.QComplex := ((999999206671558119951086842142 : Int)/10^30,(-1259625442101770636702975287 : Int)/10^30)
theorem v1255_pa_checked : Scalar.distance (sourceCoefficient 13 86 1 0) v1255_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1255_pb : Scalar.QComplex := ((-543499924911548880300779 : Int)/10^30,(-431477068953715681036531179 : Int)/10^30)
theorem v1255_pb_checked : Scalar.distance (sourceCoefficient 13 86 1 1) v1255_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1255_pg : Scalar.QComplex := ((-93086344210894457266599 : Int)/10^30,(117254020501234916884 : Int)/10^30)
theorem v1255_pg_checked : Scalar.distance (sourceCoefficient 13 86 1 2) v1255_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1255_mb : Scalar.QComplex := ((-915845000042945703802127 : Int)/10^30,(-431476439279126562628195179 : Int)/10^30)
theorem v1255_mb_checked : Scalar.distance (sourceCoefficient 13 86 3 1) v1255_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1255_mg : Scalar.QComplex := ((-93086208365655483936130 : Int)/10^30,(197583299442894151196 : Int)/10^30)
theorem v1255_mg_checked : Scalar.distance (sourceCoefficient 13 86 3 2) v1255_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1255_upper : Scalar.QComplex := ((999995543290967200973902509870 : Int)/10^30,(-2985531477533380347485964572 : Int)/10^30)
theorem v1255_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 86 5) 1) 14) v1255_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1255 : Material (13 : Basis) (86 : Basis) where
  plus := ![v1255_pa,v1255_pb,v1255_pg]
  minus := ![(Primitive.Addresses.material1255 1).one,v1255_mb,v1255_mg]
  upper := v1255_upper
  lower := (Primitive.Addresses.material1255 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1255_pa_checked.trans (by decide +kernel)
    · exact v1255_pb_checked.trans (by decide +kernel)
    · exact v1255_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 86 Primitive.Addresses.material1255
    · exact v1255_mb_checked.trans (by decide +kernel)
    · exact v1255_mg_checked.trans (by decide +kernel)
  upper_error := v1255_upper_checked
  lower_error := reuse_lower_error 13 86 Primitive.Addresses.material1255

def v1256_pa : Scalar.QComplex := ((999999205454600394348856561210 : Int)/10^30,(-1260591197775436734535763070 : Int)/10^30)
theorem v1256_pa_checked : Scalar.distance (sourceCoefficient 13 87 1 0) v1256_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1256_pb : Scalar.QComplex := ((-543916626453140349360741 : Int)/10^30,(-431477068256969482197972232 : Int)/10^30)
theorem v1256_pb_checked : Scalar.distance (sourceCoefficient 13 87 1 1) v1256_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1256_pg : Scalar.QComplex := ((-93086344079095747331940 : Int)/10^30,(117343919214274924889 : Int)/10^30)
theorem v1256_pg_checked : Scalar.distance (sourceCoefficient 13 87 1 2) v1256_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1256_mb : Scalar.QComplex := ((-916261700828119555412560 : Int)/10^30,(-431476438222785960367400555 : Int)/10^30)
theorem v1256_mb_checked : Scalar.distance (sourceCoefficient 13 87 3 1) v1256_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1256_mg : Scalar.QComplex := ((-93086208156278282610361 : Int)/10^30,(197673198008724409081 : Int)/10^30)
theorem v1256_mg_checked : Scalar.distance (sourceCoefficient 13 87 3 2) v1256_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1256_upper : Scalar.QComplex := ((999995540407204607809888123859 : Int)/10^30,(-2986497229668308182176656998 : Int)/10^30)
theorem v1256_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 87 5) 1) 14) v1256_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1256 : Material (13 : Basis) (87 : Basis) where
  plus := ![v1256_pa,v1256_pb,v1256_pg]
  minus := ![(Primitive.Addresses.material1256 1).one,v1256_mb,v1256_mg]
  upper := v1256_upper
  lower := (Primitive.Addresses.material1256 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1256_pa_checked.trans (by decide +kernel)
    · exact v1256_pb_checked.trans (by decide +kernel)
    · exact v1256_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 87 Primitive.Addresses.material1256
    · exact v1256_mb_checked.trans (by decide +kernel)
    · exact v1256_mg_checked.trans (by decide +kernel)
  upper_error := v1256_upper_checked
  lower_error := reuse_lower_error 13 87 Primitive.Addresses.material1256

def v1257_pa : Scalar.QComplex := ((999999190561416303926637251557 : Int)/10^30,(-1272350781899915346451096322 : Int)/10^30)
theorem v1257_pa_checked : Scalar.distance (sourceCoefficient 13 88 1 0) v1257_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1257_pb : Scalar.QComplex := ((-548990618693467700394930 : Int)/10^30,(-431477059729950379957992209 : Int)/10^30)
theorem v1257_pb_checked : Scalar.distance (sourceCoefficient 13 88 1 1) v1257_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1257_pg : Scalar.QComplex := ((-93086342466114760646379 : Int)/10^30,(118438576489718018691 : Int)/10^30)
theorem v1257_pg_checked : Scalar.distance (sourceCoefficient 13 88 1 2) v1257_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1257_mb : Scalar.QComplex := ((-921335683820734259922679 : Int)/10^30,(-431476425317143253851122360 : Int)/10^30)
theorem v1257_mb_checked : Scalar.distance (sourceCoefficient 13 88 3 1) v1257_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1257_mg : Scalar.QComplex := ((-93086205598657969337474 : Int)/10^30,(198767853484646625384 : Int)/10^30)
theorem v1257_mg_checked : Scalar.distance (sourceCoefficient 13 88 3 2) v1257_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1257_upper : Scalar.QComplex := ((999995505218067321324034334625 : Int)/10^30,(-2998256770573982977506581689 : Int)/10^30)
theorem v1257_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 88 5) 1) 14) v1257_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1257 : Material (13 : Basis) (88 : Basis) where
  plus := ![v1257_pa,v1257_pb,v1257_pg]
  minus := ![(Primitive.Addresses.material1257 1).one,v1257_mb,v1257_mg]
  upper := v1257_upper
  lower := (Primitive.Addresses.material1257 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1257_pa_checked.trans (by decide +kernel)
    · exact v1257_pb_checked.trans (by decide +kernel)
    · exact v1257_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 88 Primitive.Addresses.material1257
    · exact v1257_mb_checked.trans (by decide +kernel)
    · exact v1257_mg_checked.trans (by decide +kernel)
  upper_error := v1257_upper_checked
  lower_error := reuse_lower_error 13 88 Primitive.Addresses.material1257

def v1258_pa : Scalar.QComplex := ((999999169960512434610578000519 : Int)/10^30,(-1288440253238475907476879573 : Int)/10^30)
theorem v1258_pa_checked : Scalar.distance (sourceCoefficient 13 89 1 0) v1258_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1258_pb : Scalar.QComplex := ((-555932858353396006213026 : Int)/10^30,(-431477047934386645739470445 : Int)/10^30)
theorem v1258_pb_checked : Scalar.distance (sourceCoefficient 13 89 1 1) v1258_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1258_pg : Scalar.QComplex := ((-93086340234902241218926 : Int)/10^30,(119936287337154854395 : Int)/10^30)
theorem v1258_pg_checked : Scalar.distance (sourceCoefficient 13 89 1 2) v1258_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1258_mb : Scalar.QComplex := ((-928277910716709214162240 : Int)/10^30,(-431476407530743752009478287 : Int)/10^30)
theorem v1258_mb_checked : Scalar.distance (sourceCoefficient 13 89 3 1) v1258_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1258_mg : Scalar.QComplex := ((-93086202074989273746969 : Int)/10^30,(200265561848981349636 : Int)/10^30)
theorem v1258_mg_checked : Scalar.distance (sourceCoefficient 13 89 3 2) v1258_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1258_upper : Scalar.QComplex := ((999995456848226229716673953656 : Int)/10^30,(-3014346182393874802775705873 : Int)/10^30)
theorem v1258_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 89 5) 1) 14) v1258_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1258 : Material (13 : Basis) (89 : Basis) where
  plus := ![v1258_pa,v1258_pb,v1258_pg]
  minus := ![(Primitive.Addresses.material1258 1).one,v1258_mb,v1258_mg]
  upper := v1258_upper
  lower := (Primitive.Addresses.material1258 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1258_pa_checked.trans (by decide +kernel)
    · exact v1258_pb_checked.trans (by decide +kernel)
    · exact v1258_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 89 Primitive.Addresses.material1258
    · exact v1258_mb_checked.trans (by decide +kernel)
    · exact v1258_mg_checked.trans (by decide +kernel)
  upper_error := v1258_upper_checked
  lower_error := reuse_lower_error 13 89 Primitive.Addresses.material1258

def v1259_pa : Scalar.QComplex := ((999999135856290831387975477831 : Int)/10^30,(-1314643172725159651470718515 : Int)/10^30)
theorem v1259_pa_checked : Scalar.distance (sourceCoefficient 13 90 1 0) v1259_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1259_pb : Scalar.QComplex := ((-567238819757083402707153 : Int)/10^30,(-431477028405648602767074420 : Int)/10^30)
theorem v1259_pb_checked : Scalar.distance (sourceCoefficient 13 90 1 1) v1259_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1259_pg : Scalar.QComplex := ((-93086336541029133275108 : Int)/10^30,(122375422557612063287 : Int)/10^30)
theorem v1259_pg_checked : Scalar.distance (sourceCoefficient 13 90 1 2) v1259_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1259_mb : Scalar.QComplex := ((-939583851058249082727664 : Int)/10^30,(-431476378245477490695710106 : Int)/10^30)
theorem v1259_mb_checked : Scalar.distance (sourceCoefficient 13 90 3 1) v1259_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1259_mg : Scalar.QComplex := ((-93086196276253700518692 : Int)/10^30,(202704692973590915678 : Int)/10^30)
theorem v1259_mg_checked : Scalar.distance (sourceCoefficient 13 90 3 2) v1259_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1259_upper : Scalar.QComplex := ((999995377520193496996709433804 : Int)/10^30,(-3040549003993595406148831242 : Int)/10^30)
theorem v1259_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 90 5) 1) 14) v1259_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1259 : Material (13 : Basis) (90 : Basis) where
  plus := ![v1259_pa,v1259_pb,v1259_pg]
  minus := ![(Primitive.Addresses.material1259 1).one,v1259_mb,v1259_mg]
  upper := v1259_upper
  lower := (Primitive.Addresses.material1259 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1259_pa_checked.trans (by decide +kernel)
    · exact v1259_pb_checked.trans (by decide +kernel)
    · exact v1259_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 90 Primitive.Addresses.material1259
    · exact v1259_mb_checked.trans (by decide +kernel)
    · exact v1259_mg_checked.trans (by decide +kernel)
  upper_error := v1259_upper_checked
  lower_error := reuse_lower_error 13 90 Primitive.Addresses.material1259

def v1260_pa : Scalar.QComplex := ((999999116341805121564539134687 : Int)/10^30,(-1329404230813587243232135211 : Int)/10^30)
theorem v1260_pa_checked : Scalar.distance (sourceCoefficient 13 91 1 0) v1260_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1260_pb : Scalar.QComplex := ((-573607879078309900431372 : Int)/10^30,(-431477017230464739139276606 : Int)/10^30)
theorem v1260_pb_checked : Scalar.distance (sourceCoefficient 13 91 1 1) v1260_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1260_pg : Scalar.QComplex := ((-93086334427302002698702 : Int)/10^30,(123749476170822494345 : Int)/10^30)
theorem v1260_pg_checked : Scalar.distance (sourceCoefficient 13 91 1 2) v1260_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1260_mb : Scalar.QComplex := ((-945952898364303352055239 : Int)/10^30,(-431476361574086445664517626 : Int)/10^30)
theorem v1260_mb_checked : Scalar.distance (sourceCoefficient 13 91 3 1) v1260_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1260_mg : Scalar.QComplex := ((-93086192976780973856353 : Int)/10^30,(204078744251127074235 : Int)/10^30)
theorem v1260_mg_checked : Scalar.distance (sourceCoefficient 13 91 3 2) v1260_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1260_upper : Scalar.QComplex := ((999995332529489703810589543470 : Int)/10^30,(-3055310006416928936043364793 : Int)/10^30)
theorem v1260_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 91 5) 1) 14) v1260_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1260 : Material (13 : Basis) (91 : Basis) where
  plus := ![v1260_pa,v1260_pb,v1260_pg]
  minus := ![(Primitive.Addresses.material1260 1).one,v1260_mb,v1260_mg]
  upper := v1260_upper
  lower := (Primitive.Addresses.material1260 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1260_pa_checked.trans (by decide +kernel)
    · exact v1260_pb_checked.trans (by decide +kernel)
    · exact v1260_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 91 Primitive.Addresses.material1260
    · exact v1260_mb_checked.trans (by decide +kernel)
    · exact v1260_mg_checked.trans (by decide +kernel)
  upper_error := v1260_upper_checked
  lower_error := reuse_lower_error 13 91 Primitive.Addresses.material1260

def v1261_pa : Scalar.QComplex := ((999999073348628561043338552657 : Int)/10^30,(-1361360306529887455420886992 : Int)/10^30)
theorem v1261_pa_checked : Scalar.distance (sourceCoefficient 13 92 1 0) v1261_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1261_pb : Scalar.QComplex := ((-587396195228883029716846 : Int)/10^30,(-431476992607979637362480899 : Int)/10^30)
theorem v1261_pb_checked : Scalar.distance (sourceCoefficient 13 92 1 1) v1261_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1261_pg : Scalar.QComplex := ((-93086329770248980944521 : Int)/10^30,(126724151858877455279 : Int)/10^30)
theorem v1261_pg_checked : Scalar.distance (sourceCoefficient 13 92 1 2) v1261_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1261_mb : Scalar.QComplex := ((-959741188132760534033104 : Int)/10^30,(-431476325052914676726335636 : Int)/10^30)
theorem v1261_mb_checked : Scalar.distance (sourceCoefficient 13 92 3 1) v1261_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1261_mg : Scalar.QComplex := ((-93086185752718541764045 : Int)/10^30,(207053414812747315218 : Int)/10^30)
theorem v1261_mg_checked : Scalar.distance (sourceCoefficient 13 92 3 2) v1261_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1261_upper : Scalar.QComplex := ((999995234383089522784359640101 : Int)/10^30,(-3087265960336085760198789851 : Int)/10^30)
theorem v1261_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 92 5) 1) 14) v1261_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1261 : Material (13 : Basis) (92 : Basis) where
  plus := ![v1261_pa,v1261_pb,v1261_pg]
  minus := ![(Primitive.Addresses.material1261 1).one,v1261_mb,v1261_mg]
  upper := v1261_upper
  lower := (Primitive.Addresses.material1261 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1261_pa_checked.trans (by decide +kernel)
    · exact v1261_pb_checked.trans (by decide +kernel)
    · exact v1261_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 92 Primitive.Addresses.material1261
    · exact v1261_mb_checked.trans (by decide +kernel)
    · exact v1261_mg_checked.trans (by decide +kernel)
  upper_error := v1261_upper_checked
  lower_error := reuse_lower_error 13 92 Primitive.Addresses.material1261

def v1262_pa : Scalar.QComplex := ((999999020999030859284932085486 : Int)/10^30,(-1399285882097912312589209850 : Int)/10^30)
theorem v1262_pa_checked : Scalar.distance (sourceCoefficient 13 93 1 0) v1262_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1262_pb : Scalar.QComplex := ((-603760213331482044125444 : Int)/10^30,(-431476962623568553062985562 : Int)/10^30)
theorem v1262_pb_checked : Scalar.distance (sourceCoefficient 13 93 1 1) v1262_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1262_pg : Scalar.QComplex := ((-93086324099330369787649 : Int)/10^30,(130254506647871892573 : Int)/10^30)
theorem v1262_pg_checked : Scalar.distance (sourceCoefficient 13 93 1 2) v1262_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1262_mb : Scalar.QComplex := ((-976105174267091418264941 : Int)/10^30,(-431476280947104142466810304 : Int)/10^30)
theorem v1262_mb_checked : Scalar.distance (sourceCoefficient 13 93 3 1) v1262_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1262_mg : Scalar.QComplex := ((-93086177035264860524438 : Int)/10^30,(210583763393481966650 : Int)/10^30)
theorem v1262_mg_checked : Scalar.distance (sourceCoefficient 13 93 3 2) v1262_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1262_upper : Scalar.QComplex := ((999995116577466940530595474597 : Int)/10^30,(-3125191389067764345020992963 : Int)/10^30)
theorem v1262_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 93 5) 1) 14) v1262_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1262 : Material (13 : Basis) (93 : Basis) where
  plus := ![v1262_pa,v1262_pb,v1262_pg]
  minus := ![(Primitive.Addresses.material1262 1).one,v1262_mb,v1262_mg]
  upper := v1262_upper
  lower := (Primitive.Addresses.material1262 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1262_pa_checked.trans (by decide +kernel)
    · exact v1262_pb_checked.trans (by decide +kernel)
    · exact v1262_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 93 Primitive.Addresses.material1262
    · exact v1262_mb_checked.trans (by decide +kernel)
    · exact v1262_mg_checked.trans (by decide +kernel)
  upper_error := v1262_upper_checked
  lower_error := reuse_lower_error 13 93 Primitive.Addresses.material1262

def v1263_pa : Scalar.QComplex := ((999998957309587442242775287275 : Int)/10^30,(-1444084394317803716068164027 : Int)/10^30)
theorem v1263_pa_checked : Scalar.distance (sourceCoefficient 13 94 1 0) v1263_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1263_pb : Scalar.QComplex := ((-623089745235707315251215 : Int)/10^30,(-431476926139317328845094164 : Int)/10^30)
theorem v1263_pb_checked : Scalar.distance (sourceCoefficient 13 94 1 1) v1263_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1263_pg : Scalar.QComplex := ((-93086317199485109065499 : Int)/10^30,(134424638155574824722 : Int)/10^30)
theorem v1263_pg_checked : Scalar.distance (sourceCoefficient 13 94 1 2) v1263_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1263_mb : Scalar.QComplex := ((-995434667489782941375645 : Int)/10^30,(-431476227782351039456549611 : Int)/10^30)
theorem v1263_mb_checked : Scalar.distance (sourceCoefficient 13 94 3 1) v1263_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1263_mg : Scalar.QComplex := ((-93086166536786493533445 : Int)/10^30,(214753887394198651547 : Int)/10^30)
theorem v1263_mg_checked : Scalar.distance (sourceCoefficient 13 94 3 2) v1263_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1263_upper : Scalar.QComplex := ((999994975569950379182023686228 : Int)/10^30,(-3169989724643332723238549295 : Int)/10^30)
theorem v1263_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 94 5) 1) 14) v1263_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1263 : Material (13 : Basis) (94 : Basis) where
  plus := ![v1263_pa,v1263_pb,v1263_pg]
  minus := ![(Primitive.Addresses.material1263 1).one,v1263_mb,v1263_mg]
  upper := v1263_upper
  lower := (Primitive.Addresses.material1263 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1263_pa_checked.trans (by decide +kernel)
    · exact v1263_pb_checked.trans (by decide +kernel)
    · exact v1263_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 94 Primitive.Addresses.material1263
    · exact v1263_mb_checked.trans (by decide +kernel)
    · exact v1263_mg_checked.trans (by decide +kernel)
  upper_error := v1263_upper_checked
  lower_error := reuse_lower_error 13 94 Primitive.Addresses.material1263

def v1264_pa : Scalar.QComplex := ((999998892393769566127166354445 : Int)/10^30,(-1488358570397665957337002891 : Int)/10^30)
theorem v1264_pa_checked : Scalar.distance (sourceCoefficient 13 95 1 0) v1264_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1264_pb : Scalar.QComplex := ((-642193036890838054829470 : Int)/10^30,(-431476888947698660528503935 : Int)/10^30)
theorem v1264_pb_checked : Scalar.distance (sourceCoefficient 13 95 1 1) v1264_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1264_pg : Scalar.QComplex := ((-93086310166257141684745 : Int)/10^30,(138545960977013777886 : Int)/10^30)
theorem v1264_pg_checked : Scalar.distance (sourceCoefficient 13 95 1 2) v1264_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1264_mb : Scalar.QComplex := ((-1014537919937193271756758 : Int)/10^30,(-431476174105465901218830694 : Int)/10^30)
theorem v1264_mb_checked : Scalar.distance (sourceCoefficient 13 95 3 1) v1264_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1264_mg : Scalar.QComplex := ((-93086155947045167532513 : Int)/10^30,(218875202611721793512 : Int)/10^30)
theorem v1264_mg_checked : Scalar.distance (sourceCoefficient 13 95 3 2) v1264_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1264_upper : Scalar.QComplex := ((999994834241017795587983179683 : Int)/10^30,(-3214263722743197966430823867 : Int)/10^30)
theorem v1264_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 95 5) 1) 14) v1264_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1264 : Material (13 : Basis) (95 : Basis) where
  plus := ![v1264_pa,v1264_pb,v1264_pg]
  minus := ![(Primitive.Addresses.material1264 1).one,v1264_mb,v1264_mg]
  upper := v1264_upper
  lower := (Primitive.Addresses.material1264 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1264_pa_checked.trans (by decide +kernel)
    · exact v1264_pb_checked.trans (by decide +kernel)
    · exact v1264_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 95 Primitive.Addresses.material1264
    · exact v1264_mb_checked.trans (by decide +kernel)
    · exact v1264_mg_checked.trans (by decide +kernel)
  upper_error := v1264_upper_checked
  lower_error := reuse_lower_error 13 95 Primitive.Addresses.material1264

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
