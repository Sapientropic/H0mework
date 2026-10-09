import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B178

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4273_pa : Scalar.QComplex := ((999998116899524105233440864518 : Int)/10^30,(-1940669319003660345952699358 : Int)/10^30)
theorem v4273_pa_checked : Scalar.distance (sourceCoefficient 66 83 1 0) v4273_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4273_pb : Scalar.QComplex := ((-837355174557437804074335 : Int)/10^30,(-431476702153155824697959501 : Int)/10^30)
theorem v4273_pb_checked : Scalar.distance (sourceCoefficient 66 83 1 1) v4273_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4273_pg : Scalar.QComplex := ((-93086253922849720849688 : Int)/10^30,(180649977191116593164 : Int)/10^30)
theorem v4273_pg_checked : Scalar.distance (sourceCoefficient 66 83 1 2) v4273_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4273_mb : Scalar.QComplex := ((-1209699823740732263995849 : Int)/10^30,(-431475818894857587646599406 : Int)/10^30)
theorem v4273_mb_checked : Scalar.distance (sourceCoefficient 66 83 3 1) v4273_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4273_mg : Scalar.QComplex := ((-93086063369788990414283 : Int)/10^30,(260979154613047628534 : Int)/10^30)
theorem v4273_mg_checked : Scalar.distance (sourceCoefficient 66 83 3 2) v4273_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4273_upper : Scalar.QComplex := ((999993278100608558909507720196 : Int)/10^30,(-3666572459252749082163034560 : Int)/10^30)
theorem v4273_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 66 83 5) 1) 14) v4273_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4273 : Material (66 : Basis) (83 : Basis) where
  plus := ![v4273_pa,v4273_pb,v4273_pg]
  minus := ![(Primitive.Addresses.material4273 1).one,v4273_mb,v4273_mg]
  upper := v4273_upper
  lower := (Primitive.Addresses.material4273 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4273_pa_checked.trans (by decide +kernel)
    · exact v4273_pb_checked.trans (by decide +kernel)
    · exact v4273_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 66 83 Primitive.Addresses.material4273
    · exact v4273_mb_checked.trans (by decide +kernel)
    · exact v4273_mg_checked.trans (by decide +kernel)
  upper_error := v4273_upper_checked
  lower_error := reuse_lower_error 66 83 Primitive.Addresses.material4273

def v4274_pa : Scalar.QComplex := ((999998048088858431391333408127 : Int)/10^30,(-1975808308814423614836676777 : Int)/10^30)
theorem v4274_pa_checked : Scalar.distance (sourceCoefficient 66 84 1 0) v4274_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4274_pb : Scalar.QComplex := ((-852516855410467183787087 : Int)/10^30,(-431476670874446967377732049 : Int)/10^30)
theorem v4274_pb_checked : Scalar.distance (sourceCoefficient 66 84 1 1) v4274_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4274_pg : Scalar.QComplex := ((-93086247346165022170588 : Int)/10^30,(183920939940239277923 : Int)/10^30)
theorem v4274_pg_checked : Scalar.distance (sourceCoefficient 66 84 1 2) v4274_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4274_mb : Scalar.QComplex := ((-1224861471956257935964349 : Int)/10^30,(-431475774532312657411618555 : Int)/10^30)
theorem v4274_mb_checked : Scalar.distance (sourceCoefficient 66 84 3 1) v4274_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4274_mg : Scalar.QComplex := ((-93086053970413206736082 : Int)/10^30,(264250110468858699335 : Int)/10^30)
theorem v4274_mg_checked : Scalar.distance (sourceCoefficient 66 84 3 2) v4274_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4274_upper : Scalar.QComplex := ((999993148643336741347479174481 : Int)/10^30,(-3701711277967148245389580906 : Int)/10^30)
theorem v4274_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 66 84 5) 1) 14) v4274_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4274 : Material (66 : Basis) (84 : Basis) where
  plus := ![v4274_pa,v4274_pb,v4274_pg]
  minus := ![(Primitive.Addresses.material4274 1).one,v4274_mb,v4274_mg]
  upper := v4274_upper
  lower := (Primitive.Addresses.material4274 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4274_pa_checked.trans (by decide +kernel)
    · exact v4274_pb_checked.trans (by decide +kernel)
    · exact v4274_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 66 84 Primitive.Addresses.material4274
    · exact v4274_mb_checked.trans (by decide +kernel)
    · exact v4274_mg_checked.trans (by decide +kernel)
  upper_error := v4274_upper_checked
  lower_error := reuse_lower_error 66 84 Primitive.Addresses.material4274

def v4275_pa : Scalar.QComplex := ((999997888762757725429131109774 : Int)/10^30,(-2054864965691528979659056946 : Int)/10^30)
theorem v4275_pa_checked : Scalar.distance (sourceCoefficient 66 85 1 0) v4275_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4275_pb : Scalar.QComplex := ((-886628016434579998374882 : Int)/10^30,(-431476597905844915781469963 : Int)/10^30)
theorem v4275_pb_checked : Scalar.distance (sourceCoefficient 66 85 1 1) v4275_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4275_pg : Scalar.QComplex := ((-93086232059537824858910 : Int)/10^30,(191280040884921917521 : Int)/10^30)
theorem v4275_pg_checked : Scalar.distance (sourceCoefficient 66 85 1 2) v4275_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4275_mb : Scalar.QComplex := ((-1258972557310609357514627 : Int)/10^30,(-431475672127342121213401791 : Int)/10^30)
theorem v4275_mb_checked : Scalar.distance (sourceCoefficient 66 85 3 1) v4275_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4275_mg : Scalar.QComplex := ((-93086032333219027676083 : Int)/10^30,(271609195481740942551 : Int)/10^30)
theorem v4275_mg_checked : Scalar.distance (sourceCoefficient 66 85 3 2) v4275_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4275_upper : Scalar.QComplex := ((999992852872855526900243856899 : Int)/10^30,(-3780767542116253971488910476 : Int)/10^30)
theorem v4275_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 66 85 5) 1) 14) v4275_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4275 : Material (66 : Basis) (85 : Basis) where
  plus := ![v4275_pa,v4275_pb,v4275_pg]
  minus := ![(Primitive.Addresses.material4275 1).one,v4275_mb,v4275_mg]
  upper := v4275_upper
  lower := (Primitive.Addresses.material4275 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4275_pa_checked.trans (by decide +kernel)
    · exact v4275_pb_checked.trans (by decide +kernel)
    · exact v4275_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 66 85 Primitive.Addresses.material4275
    · exact v4275_mb_checked.trans (by decide +kernel)
    · exact v4275_mg_checked.trans (by decide +kernel)
  upper_error := v4275_upper_checked
  lower_error := reuse_lower_error 66 85 Primitive.Addresses.material4275

def v4276_pa : Scalar.QComplex := ((999997858686927829858972965393 : Int)/10^30,(-2069449578781422982495830953 : Int)/10^30)
theorem v4276_pa_checked : Scalar.distance (sourceCoefficient 66 86 1 0) v4276_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4276_pb : Scalar.QComplex := ((-892920947142763209537577 : Int)/10^30,(-431476584051520659474858247 : Int)/10^30)
theorem v4276_pb_checked : Scalar.distance (sourceCoefficient 66 86 1 1) v4276_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4276_pg : Scalar.QComplex := ((-93086229165254568734768 : Int)/10^30,(192637670233948542709 : Int)/10^30)
theorem v4276_pg_checked : Scalar.distance (sourceCoefficient 66 86 1 2) v4276_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4276_mb : Scalar.QComplex := ((-1265265473719989007288398 : Int)/10^30,(-431475652842507245420710731 : Int)/10^30)
theorem v4276_mb_checked : Scalar.distance (sourceCoefficient 66 86 3 1) v4276_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4276_mg : Scalar.QComplex := ((-93086028267363866371952 : Int)/10^30,(272966821827624018014 : Int)/10^30)
theorem v4276_mg_checked : Scalar.distance (sourceCoefficient 66 86 3 2) v4276_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4276_upper : Scalar.QComplex := ((999992797625351338352691265159 : Int)/10^30,(-3795352081575926064150368726 : Int)/10^30)
theorem v4276_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 66 86 5) 1) 14) v4276_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4276 : Material (66 : Basis) (86 : Basis) where
  plus := ![v4276_pa,v4276_pb,v4276_pg]
  minus := ![(Primitive.Addresses.material4276 1).one,v4276_mb,v4276_mg]
  upper := v4276_upper
  lower := (Primitive.Addresses.material4276 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4276_pa_checked.trans (by decide +kernel)
    · exact v4276_pb_checked.trans (by decide +kernel)
    · exact v4276_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 66 86 Primitive.Addresses.material4276
    · exact v4276_mb_checked.trans (by decide +kernel)
    · exact v4276_mg_checked.trans (by decide +kernel)
  upper_error := v4276_upper_checked
  lower_error := reuse_lower_error 66 86 Primitive.Addresses.material4276

def v4277_pa : Scalar.QComplex := ((999997856687877229283014777271 : Int)/10^30,(-2070415333152886586428956957 : Int)/10^30)
theorem v4277_pa_checked : Scalar.distance (sourceCoefficient 66 87 1 0) v4277_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4277_pb : Scalar.QComplex := ((-893337648309773970848361 : Int)/10^30,(-431476583129804148870140173 : Int)/10^30)
theorem v4277_pb_checked : Scalar.distance (sourceCoefficient 66 87 1 1) v4277_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4277_pg : Scalar.QComplex := ((-93086228972787333567229 : Int)/10^30,(192727568845974070661 : Int)/10^30)
theorem v4277_pg_checked : Scalar.distance (sourceCoefficient 66 87 1 2) v4277_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4277_mb : Scalar.QComplex := ((-1265682173936443043855688 : Int)/10^30,(-431475651561196738406765999 : Int)/10^30)
theorem v4277_mb_checked : Scalar.distance (sourceCoefficient 66 87 3 1) v4277_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4277_mg : Scalar.QComplex := ((-93086027997318249573915 : Int)/10^30,(273056720240085628593 : Int)/10^30)
theorem v4277_mg_checked : Scalar.distance (sourceCoefficient 66 87 3 2) v4277_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4277_upper : Scalar.QComplex := ((999992793959499282533784746028 : Int)/10^30,(-3796317831058831993125771731 : Int)/10^30)
theorem v4277_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 66 87 5) 1) 14) v4277_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4277 : Material (66 : Basis) (87 : Basis) where
  plus := ![v4277_pa,v4277_pb,v4277_pg]
  minus := ![(Primitive.Addresses.material4277 1).one,v4277_mb,v4277_mg]
  upper := v4277_upper
  lower := (Primitive.Addresses.material4277 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4277_pa_checked.trans (by decide +kernel)
    · exact v4277_pb_checked.trans (by decide +kernel)
    · exact v4277_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 66 87 Primitive.Addresses.material4277
    · exact v4277_mb_checked.trans (by decide +kernel)
    · exact v4277_mg_checked.trans (by decide +kernel)
  upper_error := v4277_upper_checked
  lower_error := reuse_lower_error 66 87 Primitive.Addresses.material4277

def v4278_pa : Scalar.QComplex := ((999997832271490548912620834796 : Int)/10^30,(-2082174901360422236731082225 : Int)/10^30)
theorem v4278_pa_checked : Scalar.distance (sourceCoefficient 66 88 1 0) v4278_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4278_pb : Scalar.QComplex := ((-898411635971566277235266 : Int)/10^30,(-431476571863420040308568577 : Int)/10^30)
theorem v4278_pb_checked : Scalar.distance (sourceCoefficient 66 88 1 1) v4278_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4278_pg : Scalar.QComplex := ((-93086226621072272265317 : Int)/10^30,(193822224886707721182 : Int)/10^30)
theorem v4278_pg_checked : Scalar.distance (sourceCoefficient 66 88 1 2) v4278_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4278_mb : Scalar.QComplex := ((-1270756149986575784480773 : Int)/10^30,(-431475635916193996629217217 : Int)/10^30)
theorem v4278_mb_checked : Scalar.distance (sourceCoefficient 66 88 3 1) v4278_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4278_mg : Scalar.QComplex := ((-93086024700965202247776 : Int)/10^30,(274151373843804626307 : Int)/10^30)
theorem v4278_mg_checked : Scalar.distance (sourceCoefficient 66 88 3 2) v4278_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4278_upper : Scalar.QComplex := ((999992749247201060990918051626 : Int)/10^30,(-3808077339611403801198990197 : Int)/10^30)
theorem v4278_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 66 88 5) 1) 14) v4278_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4278 : Material (66 : Basis) (88 : Basis) where
  plus := ![v4278_pa,v4278_pb,v4278_pg]
  minus := ![(Primitive.Addresses.material4278 1).one,v4278_mb,v4278_mg]
  upper := v4278_upper
  lower := (Primitive.Addresses.material4278 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4278_pa_checked.trans (by decide +kernel)
    · exact v4278_pb_checked.trans (by decide +kernel)
    · exact v4278_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 66 88 Primitive.Addresses.material4278
    · exact v4278_mb_checked.trans (by decide +kernel)
    · exact v4278_mg_checked.trans (by decide +kernel)
  upper_error := v4278_upper_checked
  lower_error := reuse_lower_error 66 88 Primitive.Addresses.material4278

def v4279_pa : Scalar.QComplex := ((999997798640934216001337305959 : Int)/10^30,(-2098264350739977857280271555 : Int)/10^30)
theorem v4279_pa_checked : Scalar.distance (sourceCoefficient 66 89 1 0) v4279_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4279_pb : Scalar.QComplex := ((-905353869314950402680741 : Int)/10^30,(-431476556319855191735432550 : Int)/10^30)
theorem v4279_pb_checked : Scalar.distance (sourceCoefficient 66 89 1 1) v4279_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4279_pg : Scalar.QComplex := ((-93086223379123275190913 : Int)/10^30,(195319934030740153609 : Int)/10^30)
theorem v4279_pg_checked : Scalar.distance (sourceCoefficient 66 89 1 2) v4279_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4279_mb : Scalar.QComplex := ((-1277698367331652752301663 : Int)/10^30,(-431475614381800226878206941 : Int)/10^30)
theorem v4279_mb_checked : Scalar.distance (sourceCoefficient 66 89 3 1) v4279_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4279_mg : Scalar.QComplex := ((-93086020166561875314984 : Int)/10^30,(275649079632515523209 : Int)/10^30)
theorem v4279_mg_checked : Scalar.distance (sourceCoefficient 66 89 3 2) v4279_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4279_upper : Scalar.QComplex := ((999992687847764811175529318732 : Int)/10^30,(-3824166706984325280022437336 : Int)/10^30)
theorem v4279_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 66 89 5) 1) 14) v4279_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4279 : Material (66 : Basis) (89 : Basis) where
  plus := ![v4279_pa,v4279_pb,v4279_pg]
  minus := ![(Primitive.Addresses.material4279 1).one,v4279_mb,v4279_mg]
  upper := v4279_upper
  lower := (Primitive.Addresses.material4279 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4279_pa_checked.trans (by decide +kernel)
    · exact v4279_pb_checked.trans (by decide +kernel)
    · exact v4279_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 66 89 Primitive.Addresses.material4279
    · exact v4279_mb_checked.trans (by decide +kernel)
    · exact v4279_mg_checked.trans (by decide +kernel)
  upper_error := v4279_upper_checked
  lower_error := reuse_lower_error 66 89 Primitive.Addresses.material4279

def v4280_pa : Scalar.QComplex := ((999997743316939486890962080796 : Int)/10^30,(-2124467234016044425617534178 : Int)/10^30)
theorem v4280_pa_checked : Scalar.distance (sourceCoefficient 66 90 1 0) v4280_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4280_pb : Scalar.QComplex := ((-916659820302593766731288 : Int)/10^30,(-431476530687214281495997642 : Int)/10^30)
theorem v4280_pb_checked : Scalar.distance (sourceCoefficient 66 90 1 1) v4280_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4280_pg : Scalar.QComplex := ((-93086218039189479235295 : Int)/10^30,(197759066442266594604 : Int)/10^30)
theorem v4280_pg_checked : Scalar.distance (sourceCoefficient 66 90 1 2) v4280_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4280_mb : Scalar.QComplex := ((-1289004291989759201921301 : Int)/10^30,(-431475578992642359636278294 : Int)/10^30)
theorem v4280_mb_checked : Scalar.distance (sourceCoefficient 66 90 3 1) v4280_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4280_mg : Scalar.QComplex := ((-93086012721768650959273 : Int)/10^30,(278088206527719129314 : Int)/10^30)
theorem v4280_mg_checked : Scalar.distance (sourceCoefficient 66 90 3 2) v4280_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4280_upper : Scalar.QComplex := ((999992587300053053167457109887 : Int)/10^30,(-3850369455750079266697747527 : Int)/10^30)
theorem v4280_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 66 90 5) 1) 14) v4280_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4280 : Material (66 : Basis) (90 : Basis) where
  plus := ![v4280_pa,v4280_pb,v4280_pg]
  minus := ![(Primitive.Addresses.material4280 1).one,v4280_mb,v4280_mg]
  upper := v4280_upper
  lower := (Primitive.Addresses.material4280 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4280_pa_checked.trans (by decide +kernel)
    · exact v4280_pb_checked.trans (by decide +kernel)
    · exact v4280_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 66 90 Primitive.Addresses.material4280
    · exact v4280_mb_checked.trans (by decide +kernel)
    · exact v4280_mg_checked.trans (by decide +kernel)
  upper_error := v4280_upper_checked
  lower_error := reuse_lower_error 66 90 Primitive.Addresses.material4280

def v4281_pa : Scalar.QComplex := ((999997711848583472808465934100 : Int)/10^30,(-2139228271460873834330097052 : Int)/10^30)
theorem v4281_pa_checked : Scalar.distance (sourceCoefficient 66 91 1 0) v4281_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4281_pb : Scalar.QComplex := ((-923028873685655061207334 : Int)/10^30,(-431476516073479848608163201 : Int)/10^30)
theorem v4281_pb_checked : Scalar.distance (sourceCoefficient 66 91 1 1) v4281_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4281_pg : Scalar.QComplex := ((-93086214998176471563939 : Int)/10^30,(199133118454111390498 : Int)/10^30)
theorem v4281_pg_checked : Scalar.distance (sourceCoefficient 66 91 1 2) v4281_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4281_mb : Scalar.QComplex := ((-1295373330390336204348306 : Int)/10^30,(-431475558882707150043701017 : Int)/10^30)
theorem v4281_mb_checked : Scalar.distance (sourceCoefficient 66 91 3 1) v4281_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4281_mg : Scalar.QComplex := ((-93086008495011774379317 : Int)/10^30,(279462255403684300441 : Int)/10^30)
theorem v4281_mg_checked : Scalar.distance (sourceCoefficient 66 91 3 2) v4281_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4281_upper : Scalar.QComplex := ((999992530355532388585586708697 : Int)/10^30,(-3865130416898549661249586396 : Int)/10^30)
theorem v4281_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 66 91 5) 1) 14) v4281_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4281 : Material (66 : Basis) (91 : Basis) where
  plus := ![v4281_pa,v4281_pb,v4281_pg]
  minus := ![(Primitive.Addresses.material4281 1).one,v4281_mb,v4281_mg]
  upper := v4281_upper
  lower := (Primitive.Addresses.material4281 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4281_pa_checked.trans (by decide +kernel)
    · exact v4281_pb_checked.trans (by decide +kernel)
    · exact v4281_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 66 91 Primitive.Addresses.material4281
    · exact v4281_mb_checked.trans (by decide +kernel)
    · exact v4281_mg_checked.trans (by decide +kernel)
  upper_error := v4281_upper_checked
  lower_error := reuse_lower_error 66 91 Primitive.Addresses.material4281

def v4282_pa : Scalar.QComplex := ((999997642976585851878948319374 : Int)/10^30,(-2171184301881548530301194884 : Int)/10^30)
theorem v4282_pa_checked : Scalar.distance (sourceCoefficient 66 92 1 0) v4282_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4282_pb : Scalar.QComplex := ((-936817176806866555304794 : Int)/10^30,(-431476484006909086915143256 : Int)/10^30)
theorem v4282_pb_checked : Scalar.distance (sourceCoefficient 66 92 1 1) v4282_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4282_pg : Scalar.QComplex := ((-93086208333651006705150 : Int)/10^30,(202107790628493139023 : Int)/10^30)
theorem v4282_pg_checked : Scalar.distance (sourceCoefficient 66 92 1 2) v4282_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4282_mb : Scalar.QComplex := ((-1309161600705525947229608 : Int)/10^30,(-431475514917463736714867999 : Int)/10^30)
theorem v4282_mb_checked : Scalar.distance (sourceCoefficient 66 92 3 1) v4282_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4282_mg : Scalar.QComplex := ((-93085999263480678797869 : Int)/10^30,(282436920719274332121 : Int)/10^30)
theorem v4282_mg_checked : Scalar.distance (sourceCoefficient 66 92 3 2) v4282_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4282_upper : Scalar.QComplex := ((999992406330427866755523328984 : Int)/10^30,(-3897086280857650989743320150 : Int)/10^30)
theorem v4282_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 66 92 5) 1) 14) v4282_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4282 : Material (66 : Basis) (92 : Basis) where
  plus := ![v4282_pa,v4282_pb,v4282_pg]
  minus := ![(Primitive.Addresses.material4282 1).one,v4282_mb,v4282_mg]
  upper := v4282_upper
  lower := (Primitive.Addresses.material4282 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4282_pa_checked.trans (by decide +kernel)
    · exact v4282_pb_checked.trans (by decide +kernel)
    · exact v4282_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 66 92 Primitive.Addresses.material4282
    · exact v4282_mb_checked.trans (by decide +kernel)
    · exact v4282_mg_checked.trans (by decide +kernel)
  upper_error := v4282_upper_checked
  lower_error := reuse_lower_error 66 92 Primitive.Addresses.material4282

def v4283_pa : Scalar.QComplex := ((999997559913918793127377251580 : Int)/10^30,(-2209109822619432731307770915 : Int)/10^30)
theorem v4283_pa_checked : Scalar.distance (sourceCoefficient 66 93 1 0) v4283_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4283_pb : Scalar.QComplex := ((-953181179137484978165478 : Int)/10^30,(-431476445187832886062845880 : Int)/10^30)
theorem v4283_pb_checked : Scalar.distance (sourceCoefficient 66 93 1 1) v4283_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4283_pg : Scalar.QComplex := ((-93086200280257552822257 : Int)/10^30,(205638141164202771941 : Int)/10^30)
theorem v4283_pg_checked : Scalar.distance (sourceCoefficient 66 93 1 2) v4283_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4283_mb : Scalar.QComplex := ((-1325525563443964015503814 : Int)/10^30,(-431475461977004985961034533 : Int)/10^30)
theorem v4283_mb_checked : Scalar.distance (sourceCoefficient 66 93 3 1) v4283_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4283_mg : Scalar.QComplex := ((-93085988163556712329734 : Int)/10^30,(285967262990757276280 : Int)/10^30)
theorem v4283_mg_checked : Scalar.distance (sourceCoefficient 66 93 3 2) v4283_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4283_upper : Scalar.QComplex := ((999992257811876302866212273421 : Int)/10^30,(-3935011601751299139174217046 : Int)/10^30)
theorem v4283_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 66 93 5) 1) 14) v4283_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4283 : Material (66 : Basis) (93 : Basis) where
  plus := ![v4283_pa,v4283_pb,v4283_pg]
  minus := ![(Primitive.Addresses.material4283 1).one,v4283_mb,v4283_mg]
  upper := v4283_upper
  lower := (Primitive.Addresses.material4283 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4283_pa_checked.trans (by decide +kernel)
    · exact v4283_pb_checked.trans (by decide +kernel)
    · exact v4283_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 66 93 Primitive.Addresses.material4283
    · exact v4283_mb_checked.trans (by decide +kernel)
    · exact v4283_mg_checked.trans (by decide +kernel)
  upper_error := v4283_upper_checked
  lower_error := reuse_lower_error 66 93 Primitive.Addresses.material4283

def v4284_pa : Scalar.QComplex := ((999997459945532492592558544042 : Int)/10^30,(-2253908268572196568703775910 : Int)/10^30)
theorem v4284_pa_checked : Scalar.distance (sourceCoefficient 66 94 1 0) v4284_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4284_pb : Scalar.QComplex := ((-972510691979861619500378 : Int)/10^30,(-431476398267883918498092260 : Int)/10^30)
theorem v4284_pb_checked : Scalar.distance (sourceCoefficient 66 94 1 1) v4284_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4284_pg : Scalar.QComplex := ((-93086190566181408211718 : Int)/10^30,(209808267531430739192 : Int)/10^30)
theorem v4284_pg_checked : Scalar.distance (sourceCoefficient 66 94 1 2) v4284_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4284_mb : Scalar.QComplex := ((-1344855028599276860291623 : Int)/10^30,(-431475398376574474807970130 : Int)/10^30)
theorem v4284_mb_checked : Scalar.distance (sourceCoefficient 66 94 3 1) v4284_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4284_mg : Scalar.QComplex := ((-93085974850852945315504 : Int)/10^30,(290137379422446405771 : Int)/10^30)
theorem v4284_mg_checked : Scalar.distance (sourceCoefficient 66 94 3 2) v4284_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4284_upper : Scalar.QComplex := ((999992080525585262299251751444 : Int)/10^30,(-3979809808445674431491662835 : Int)/10^30)
theorem v4284_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 66 94 5) 1) 14) v4284_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4284 : Material (66 : Basis) (94 : Basis) where
  plus := ![v4284_pa,v4284_pb,v4284_pg]
  minus := ![(Primitive.Addresses.material4284 1).one,v4284_mb,v4284_mg]
  upper := v4284_upper
  lower := (Primitive.Addresses.material4284 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4284_pa_checked.trans (by decide +kernel)
    · exact v4284_pb_checked.trans (by decide +kernel)
    · exact v4284_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 66 94 Primitive.Addresses.material4284
    · exact v4284_mb_checked.trans (by decide +kernel)
    · exact v4284_mg_checked.trans (by decide +kernel)
  upper_error := v4284_upper_checked
  lower_error := reuse_lower_error 66 94 Primitive.Addresses.material4284

def v4285_pa : Scalar.QComplex := ((999997359175392750488307952091 : Int)/10^30,(-2298182377563716575797317486 : Int)/10^30)
theorem v4285_pa_checked : Scalar.distance (sourceCoefficient 66 95 1 0) v4285_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4285_pb : Scalar.QComplex := ((-991613964336920146581576 : Int)/10^30,(-431476350762710535924390220 : Int)/10^30)
theorem v4285_pb_checked : Scalar.distance (sourceCoefficient 66 95 1 1) v4285_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4285_pg : Scalar.QComplex := ((-93086180751661282098865 : Int)/10^30,(213929585148691474404 : Int)/10^30)
theorem v4285_pg_checked : Scalar.distance (sourceCoefficient 66 95 1 2) v4285_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4285_mb : Scalar.QComplex := ((-1363958252848488950587126 : Int)/10^30,(-431475334386155115888078733 : Int)/10^30)
theorem v4285_mb_checked : Scalar.distance (sourceCoefficient 66 95 3 1) v4285_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4285_mg : Scalar.QComplex := ((-93085961479824987156070 : Int)/10^30,(294258687035663399300 : Int)/10^30)
theorem v4285_mg_checked : Scalar.distance (sourceCoefficient 66 95 3 2) v4285_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4285_upper : Scalar.QComplex := ((999991903342500001909733792485 : Int)/10^30,(-4024083677575990498688403239 : Int)/10^30)
theorem v4285_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 66 95 5) 1) 14) v4285_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4285 : Material (66 : Basis) (95 : Basis) where
  plus := ![v4285_pa,v4285_pb,v4285_pg]
  minus := ![(Primitive.Addresses.material4285 1).one,v4285_mb,v4285_mg]
  upper := v4285_upper
  lower := (Primitive.Addresses.material4285 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4285_pa_checked.trans (by decide +kernel)
    · exact v4285_pb_checked.trans (by decide +kernel)
    · exact v4285_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 66 95 Primitive.Addresses.material4285
    · exact v4285_mb_checked.trans (by decide +kernel)
    · exact v4285_mg_checked.trans (by decide +kernel)
  upper_error := v4285_upper_checked
  lower_error := reuse_lower_error 66 95 Primitive.Addresses.material4285

def v4286_pa : Scalar.QComplex := ((999997310080540254712344927330 : Int)/10^30,(-2319446417536709424763803203 : Int)/10^30)
theorem v4286_pa_checked : Scalar.distance (sourceCoefficient 66 96 1 0) v4286_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4286_pb : Scalar.QComplex := ((-1000788914219981311320670 : Int)/10^30,(-431476327545974278085300755 : Int)/10^30)
theorem v4286_pb_checked : Scalar.distance (sourceCoefficient 66 96 1 1) v4286_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4286_pg : Scalar.QComplex := ((-93086175962253940206222 : Int)/10^30,(215908978135603477489 : Int)/10^30)
theorem v4286_pg_checked : Scalar.distance (sourceCoefficient 66 96 1 2) v4286_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4286_mb : Scalar.QComplex := ((-1373133179280299210408092 : Int)/10^30,(-431475303251858978022292342 : Int)/10^30)
theorem v4286_mb_checked : Scalar.distance (sourceCoefficient 66 96 3 1) v4286_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4286_mg : Scalar.QComplex := ((-93085954982292429424390 : Int)/10^30,(296238075152514101475 : Int)/10^30)
theorem v4286_mg_checked : Scalar.distance (sourceCoefficient 66 96 3 2) v4286_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4286_upper : Scalar.QComplex := ((999991817547916692401190217430 : Int)/10^30,(-4045347601145432099999168393 : Int)/10^30)
theorem v4286_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 66 96 5) 1) 14) v4286_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4286 : Material (66 : Basis) (96 : Basis) where
  plus := ![v4286_pa,v4286_pb,v4286_pg]
  minus := ![(Primitive.Addresses.material4286 1).one,v4286_mb,v4286_mg]
  upper := v4286_upper
  lower := (Primitive.Addresses.material4286 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4286_pa_checked.trans (by decide +kernel)
    · exact v4286_pb_checked.trans (by decide +kernel)
    · exact v4286_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 66 96 Primitive.Addresses.material4286
    · exact v4286_mb_checked.trans (by decide +kernel)
    · exact v4286_mg_checked.trans (by decide +kernel)
  upper_error := v4286_upper_checked
  lower_error := reuse_lower_error 66 96 Primitive.Addresses.material4286

def v4287_pa : Scalar.QComplex := ((999997137708335408930928735350 : Int)/10^30,(-2392608437765896736121401424 : Int)/10^30)
theorem v4287_pa_checked : Scalar.distance (sourceCoefficient 66 97 1 0) v4287_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4287_pb : Scalar.QComplex := ((-1032356661011060899702526 : Int)/10^30,(-431476245678192831013645923 : Int)/10^30)
theorem v4287_pb_checked : Scalar.distance (sourceCoefficient 66 97 1 1) v4287_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4287_pg : Scalar.QComplex := ((-93086159108470094574413 : Int)/10^30,(222719367209932639868 : Int)/10^30)
theorem v4287_pg_checked : Scalar.distance (sourceCoefficient 66 97 1 2) v4287_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4287_mb : Scalar.QComplex := ((-1404700843669055750349670 : Int)/10^30,(-431475194142564291902840390 : Int)/10^30)
theorem v4287_mb_checked : Scalar.distance (sourceCoefficient 66 97 3 1) v4287_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4287_mg : Scalar.QComplex := ((-93085932251455816618104 : Int)/10^30,(303048447146967768790 : Int)/10^30)
theorem v4287_mg_checked : Scalar.distance (sourceCoefficient 66 97 3 2) v4287_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4287_upper : Scalar.QComplex := ((999991518904958865821509843883 : Int)/10^30,(-4118509214909596415040596939 : Int)/10^30)
theorem v4287_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 66 97 5) 1) 14) v4287_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4287 : Material (66 : Basis) (97 : Basis) where
  plus := ![v4287_pa,v4287_pb,v4287_pg]
  minus := ![(Primitive.Addresses.material4287 1).one,v4287_mb,v4287_mg]
  upper := v4287_upper
  lower := (Primitive.Addresses.material4287 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4287_pa_checked.trans (by decide +kernel)
    · exact v4287_pb_checked.trans (by decide +kernel)
    · exact v4287_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 66 97 Primitive.Addresses.material4287
    · exact v4287_mb_checked.trans (by decide +kernel)
    · exact v4287_mg_checked.trans (by decide +kernel)
  upper_error := v4287_upper_checked
  lower_error := reuse_lower_error 66 97 Primitive.Addresses.material4287

def v4288_pa : Scalar.QComplex := ((999998465021616863419646402810 : Int)/10^30,(-1752128536984237355527890272 : Int)/10^30)
theorem v4288_pa_checked : Scalar.distance (sourceCoefficient 67 68 1 0) v4288_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4288_pb : Scalar.QComplex := ((-756004077307977554094575 : Int)/10^30,(-431476858518207297226194983 : Int)/10^30)
theorem v4288_pb_checked : Scalar.distance (sourceCoefficient 67 68 1 1) v4288_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4288_pg : Scalar.QComplex := ((-93086286992573087400461 : Int)/10^30,(163099390195630180496 : Int)/10^30)
theorem v4288_pg_checked : Scalar.distance (sourceCoefficient 67 68 1 2) v4288_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4288_mb : Scalar.QComplex := ((-1128348891718000449104332 : Int)/10^30,(-431476045462183847195023305 : Int)/10^30)
theorem v4288_mb_checked : Scalar.distance (sourceCoefficient 67 68 3 1) v4288_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4288_mg : Scalar.QComplex := ((-93086111584866171605033 : Int)/10^30,(243428602690128716019 : Int)/10^30)
theorem v4288_mg_checked : Scalar.distance (sourceCoefficient 67 68 3 2) v4288_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4288_upper : Scalar.QComplex := ((999993951626468309522473870777 : Int)/10^30,(-3478032558869824064706456089 : Int)/10^30)
theorem v4288_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 67 68 5) 1) 14) v4288_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4288 : Material (67 : Basis) (68 : Basis) where
  plus := ![v4288_pa,v4288_pb,v4288_pg]
  minus := ![(Primitive.Addresses.material4288 1).one,v4288_mb,v4288_mg]
  upper := v4288_upper
  lower := (Primitive.Addresses.material4288 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4288_pa_checked.trans (by decide +kernel)
    · exact v4288_pb_checked.trans (by decide +kernel)
    · exact v4288_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 67 68 Primitive.Addresses.material4288
    · exact v4288_mb_checked.trans (by decide +kernel)
    · exact v4288_mg_checked.trans (by decide +kernel)
  upper_error := v4288_upper_checked
  lower_error := reuse_lower_error 67 68 Primitive.Addresses.material4288

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
