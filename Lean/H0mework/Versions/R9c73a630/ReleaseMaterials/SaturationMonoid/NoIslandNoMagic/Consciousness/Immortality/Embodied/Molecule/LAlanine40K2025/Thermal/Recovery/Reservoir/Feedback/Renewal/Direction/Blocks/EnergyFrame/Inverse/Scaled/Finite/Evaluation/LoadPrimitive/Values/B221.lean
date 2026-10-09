import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B147
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B148

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3537_pa : Scalar.QComplex := ((999999269016566199022002685305 : Int)/10^30,(-1209117998073461605670024487 : Int)/10^30)
theorem v3537_pa_checked : Scalar.distance (sourceCoefficient 48 58 1 0) v3537_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3537_pb : Scalar.QComplex := ((-521707235486398997762005 : Int)/10^30,(-431477204837170536288114502 : Int)/10^30)
theorem v3537_pb_checked : Scalar.distance (sourceCoefficient 48 58 1 1) v3537_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3537_pg : Scalar.QComplex := ((-93086361770296504603112 : Int)/10^30,(112552477665639525951 : Int)/10^30)
theorem v3537_pg_checked : Scalar.distance (sourceCoefficient 48 58 1 2) v3537_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3537_mb : Scalar.QComplex := ((-894052435993511645814716 : Int)/10^30,(-431476593968640289867221474 : Int)/10^30)
theorem v3537_mb_checked : Scalar.distance (sourceCoefficient 48 58 3 1) v3537_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3537_mg : Scalar.QComplex := ((-93086229982270710594778 : Int)/10^30,(192881773510871149817 : Int)/10^30)
theorem v3537_mg_checked : Scalar.distance (sourceCoefficient 48 58 3 2) v3537_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3537_upper : Scalar.QComplex := ((999995692807148817810599129716 : Int)/10^30,(-2935024216331804224996640251 : Int)/10^30)
theorem v3537_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 58 5) 1) 14) v3537_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3537 : Material (48 : Basis) (58 : Basis) where
  plus := ![v3537_pa,v3537_pb,v3537_pg]
  minus := ![(Primitive.Addresses.material3537 1).one,v3537_mb,v3537_mg]
  upper := v3537_upper
  lower := (Primitive.Addresses.material3537 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3537_pa_checked.trans (by decide +kernel)
    · exact v3537_pb_checked.trans (by decide +kernel)
    · exact v3537_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 58 Primitive.Addresses.material3537
    · exact v3537_mb_checked.trans (by decide +kernel)
    · exact v3537_mg_checked.trans (by decide +kernel)
  upper_error := v3537_upper_checked
  lower_error := reuse_lower_error 48 58 Primitive.Addresses.material3537

def v3538_pa : Scalar.QComplex := ((999999247623006900945146226207 : Int)/10^30,(-1226683912068210814999136159 : Int)/10^30)
theorem v3538_pa_checked : Scalar.distance (sourceCoefficient 48 59 1 0) v3538_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3538_pb : Scalar.QComplex := ((-529286532151667836567847 : Int)/10^30,(-431477195324321557844941067 : Int)/10^30)
theorem v3538_pb_checked : Scalar.distance (sourceCoefficient 48 59 1 1) v3538_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3538_pg : Scalar.QComplex := ((-93086359748426304471795 : Int)/10^30,(114187625848530996515 : Int)/10^30)
theorem v3538_pg_checked : Scalar.distance (sourceCoefficient 48 59 1 2) v3538_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3538_mb : Scalar.QComplex := ((-901631721627501719588291 : Int)/10^30,(-431476577915203190215441052 : Int)/10^30)
theorem v3538_mb_checked : Scalar.distance (sourceCoefficient 48 59 3 1) v3538_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3538_mg : Scalar.QComplex := ((-93086226549342025803154 : Int)/10^30,(194516919340139300867 : Int)/10^30)
theorem v3538_mg_checked : Scalar.distance (sourceCoefficient 48 59 3 2) v3538_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3538_upper : Scalar.QComplex := ((999995641096447395259457126692 : Int)/10^30,(-2952590067240845436411288886 : Int)/10^30)
theorem v3538_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 59 5) 1) 14) v3538_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3538 : Material (48 : Basis) (59 : Basis) where
  plus := ![v3538_pa,v3538_pb,v3538_pg]
  minus := ![(Primitive.Addresses.material3538 1).one,v3538_mb,v3538_mg]
  upper := v3538_upper
  lower := (Primitive.Addresses.material3538 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3538_pa_checked.trans (by decide +kernel)
    · exact v3538_pb_checked.trans (by decide +kernel)
    · exact v3538_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 59 Primitive.Addresses.material3538
    · exact v3538_mb_checked.trans (by decide +kernel)
    · exact v3538_mg_checked.trans (by decide +kernel)
  upper_error := v3538_upper_checked
  lower_error := reuse_lower_error 48 59 Primitive.Addresses.material3538

def v3539_pa : Scalar.QComplex := ((999999222560256451858151010004 : Int)/10^30,(-1246947826768918527786177641 : Int)/10^30)
theorem v3539_pa_checked : Scalar.distance (sourceCoefficient 48 60 1 0) v3539_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3539_pb : Scalar.QComplex := ((-538029955336968690533182 : Int)/10^30,(-431477184129857403470524271 : Int)/10^30)
theorem v3539_pb_checked : Scalar.distance (sourceCoefficient 48 60 1 1) v3539_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3539_pg : Scalar.QComplex := ((-93086357374385356710363 : Int)/10^30,(116073921270304298518 : Int)/10^30)
theorem v3539_pg_checked : Scalar.distance (sourceCoefficient 48 60 1 2) v3539_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3539_mb : Scalar.QComplex := ((-910375131896908142210549 : Int)/10^30,(-431476559175562784299129365 : Int)/10^30)
theorem v3539_mb_checked : Scalar.distance (sourceCoefficient 48 60 3 1) v3539_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3539_mg : Scalar.QComplex := ((-93086222547513968607403 : Int)/10^30,(196403212010868194302 : Int)/10^30)
theorem v3539_mg_checked : Scalar.distance (sourceCoefficient 48 60 3 2) v3539_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3539_upper : Scalar.QComplex := ((999995581060055828755084156415 : Int)/10^30,(-2972853908504798968962186590 : Int)/10^30)
theorem v3539_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 60 5) 1) 14) v3539_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3539 : Material (48 : Basis) (60 : Basis) where
  plus := ![v3539_pa,v3539_pb,v3539_pg]
  minus := ![(Primitive.Addresses.material3539 1).one,v3539_mb,v3539_mg]
  upper := v3539_upper
  lower := (Primitive.Addresses.material3539 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3539_pa_checked.trans (by decide +kernel)
    · exact v3539_pb_checked.trans (by decide +kernel)
    · exact v3539_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 60 Primitive.Addresses.material3539
    · exact v3539_mb_checked.trans (by decide +kernel)
    · exact v3539_mg_checked.trans (by decide +kernel)
  upper_error := v3539_upper_checked
  lower_error := reuse_lower_error 48 60 Primitive.Addresses.material3539

def v3540_pa : Scalar.QComplex := ((999999215236804782938275728320 : Int)/10^30,(-1252807157778423167822503243 : Int)/10^30)
theorem v3540_pa_checked : Scalar.distance (sourceCoefficient 48 61 1 0) v3540_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3540_pb : Scalar.QComplex := ((-540558124795725397792002 : Int)/10^30,(-431477180848937589997967279 : Int)/10^30)
theorem v3540_pb_checked : Scalar.distance (sourceCoefficient 48 61 1 1) v3540_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3540_pg : Scalar.QComplex := ((-93086356679617568229587 : Int)/10^30,(116619345458310388135 : Int)/10^30)
theorem v3540_pg_checked : Scalar.distance (sourceCoefficient 48 61 1 2) v3540_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3540_mb : Scalar.QComplex := ((-912903297583025785038247 : Int)/10^30,(-431476553712947814081498535 : Int)/10^30)
theorem v3540_mb_checked : Scalar.distance (sourceCoefficient 48 61 3 1) v3540_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3540_mg : Scalar.QComplex := ((-93086221382069929564703 : Int)/10^30,(196948635396234621327 : Int)/10^30)
theorem v3540_mg_checked : Scalar.distance (sourceCoefficient 48 61 3 2) v3540_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3540_upper : Scalar.QComplex := ((999995563623941299208095459210 : Int)/10^30,(-2978713218147905153500998301 : Int)/10^30)
theorem v3540_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 61 5) 1) 14) v3540_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3540 : Material (48 : Basis) (61 : Basis) where
  plus := ![v3540_pa,v3540_pb,v3540_pg]
  minus := ![(Primitive.Addresses.material3540 1).one,v3540_mb,v3540_mg]
  upper := v3540_upper
  lower := (Primitive.Addresses.material3540 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3540_pa_checked.trans (by decide +kernel)
    · exact v3540_pb_checked.trans (by decide +kernel)
    · exact v3540_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 61 Primitive.Addresses.material3540
    · exact v3540_mb_checked.trans (by decide +kernel)
    · exact v3540_mg_checked.trans (by decide +kernel)
  upper_error := v3540_upper_checked
  lower_error := reuse_lower_error 48 61 Primitive.Addresses.material3540

def v3541_pa : Scalar.QComplex := ((999999204534963727161793005271 : Int)/10^30,(-1261320514294860932292230373 : Int)/10^30)
theorem v3541_pa_checked : Scalar.distance (sourceCoefficient 48 62 1 0) v3541_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3541_pb : Scalar.QComplex := ((-544231446514811318172375 : Int)/10^30,(-431477176046704821179839435 : Int)/10^30)
theorem v3541_pb_checked : Scalar.distance (sourceCoefficient 48 62 1 1) v3541_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3541_pg : Scalar.QComplex := ((-93086355663505583096843 : Int)/10^30,(117411823396327559548 : Int)/10^30)
theorem v3541_pg_checked : Scalar.distance (sourceCoefficient 48 62 1 2) v3541_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3541_mb : Scalar.QComplex := ((-916576613790255555351978 : Int)/10^30,(-431476545740805630051750285 : Int)/10^30)
theorem v3541_mb_checked : Scalar.distance (sourceCoefficient 48 62 3 1) v3541_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3541_mg : Scalar.QComplex := ((-93086219682085554149454 : Int)/10^30,(197741112162317159202 : Int)/10^30)
theorem v3541_mg_checked : Scalar.distance (sourceCoefficient 48 62 3 2) v3541_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3541_upper : Scalar.QComplex := ((999995538228835160865251466527 : Int)/10^30,(-2987226543514291637009116106 : Int)/10^30)
theorem v3541_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 62 5) 1) 14) v3541_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3541 : Material (48 : Basis) (62 : Basis) where
  plus := ![v3541_pa,v3541_pb,v3541_pg]
  minus := ![(Primitive.Addresses.material3541 1).one,v3541_mb,v3541_mg]
  upper := v3541_upper
  lower := (Primitive.Addresses.material3541 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3541_pa_checked.trans (by decide +kernel)
    · exact v3541_pb_checked.trans (by decide +kernel)
    · exact v3541_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 62 Primitive.Addresses.material3541
    · exact v3541_mb_checked.trans (by decide +kernel)
    · exact v3541_mg_checked.trans (by decide +kernel)
  upper_error := v3541_upper_checked
  lower_error := reuse_lower_error 48 62 Primitive.Addresses.material3541

def v3542_pa : Scalar.QComplex := ((999999172952902248660162324697 : Int)/10^30,(-1286115668008044203546810691 : Int)/10^30)
theorem v3542_pa_checked : Scalar.distance (sourceCoefficient 48 63 1 0) v3542_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3542_pb : Scalar.QComplex := ((-554929997160972003970223 : Int)/10^30,(-431477161822631264852586887 : Int)/10^30)
theorem v3542_pb_checked : Scalar.distance (sourceCoefficient 48 63 1 1) v3542_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3542_pg : Scalar.QComplex := ((-93086352659232837158667 : Int)/10^30,(119719915646770400995 : Int)/10^30)
theorem v3542_pg_checked : Scalar.distance (sourceCoefficient 48 63 1 2) v3542_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3542_mb : Scalar.QComplex := ((-927275148178122037046466 : Int)/10^30,(-431476522284370007194665241 : Int)/10^30)
theorem v3542_mb_checked : Scalar.distance (sourceCoefficient 48 63 3 1) v3542_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3542_mg : Scalar.QComplex := ((-93086214686034267323209 : Int)/10^30,(200049200960799698458 : Int)/10^30)
theorem v3542_mg_checked : Scalar.distance (sourceCoefficient 48 63 3 2) v3542_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3542_upper : Scalar.QComplex := ((999995463852634809953498336368 : Int)/10^30,(-3012021605790233086176965613 : Int)/10^30)
theorem v3542_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 63 5) 1) 14) v3542_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3542 : Material (48 : Basis) (63 : Basis) where
  plus := ![v3542_pa,v3542_pb,v3542_pg]
  minus := ![(Primitive.Addresses.material3542 1).one,v3542_mb,v3542_mg]
  upper := v3542_upper
  lower := (Primitive.Addresses.material3542 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3542_pa_checked.trans (by decide +kernel)
    · exact v3542_pb_checked.trans (by decide +kernel)
    · exact v3542_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 63 Primitive.Addresses.material3542
    · exact v3542_mb_checked.trans (by decide +kernel)
    · exact v3542_mg_checked.trans (by decide +kernel)
  upper_error := v3542_upper_checked
  lower_error := reuse_lower_error 48 63 Primitive.Addresses.material3542

def v3543_pa : Scalar.QComplex := ((999999126748572622295871503990 : Int)/10^30,(-1321552909340883271695840740 : Int)/10^30)
theorem v3543_pa_checked : Scalar.distance (sourceCoefficient 48 64 1 0) v3543_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3543_pb : Scalar.QComplex := ((-570220368789267024476994 : Int)/10^30,(-431477140879595854276698451 : Int)/10^30)
theorem v3543_pb_checked : Scalar.distance (sourceCoefficient 48 64 1 1) v3543_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3543_pg : Scalar.QComplex := ((-93086348249622437234219 : Int)/10^30,(123018641775411693465 : Int)/10^30)
theorem v3543_pg_checked : Scalar.distance (sourceCoefficient 48 64 1 2) v3543_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3543_mb : Scalar.QComplex := ((-942565496040216575807157 : Int)/10^30,(-431476488146440332223547253 : Int)/10^30)
theorem v3543_mb_checked : Scalar.distance (sourceCoefficient 48 64 3 1) v3543_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3543_mg : Scalar.QComplex := ((-93086207429773429390496 : Int)/10^30,(203347922055879320349 : Int)/10^30)
theorem v3543_mg_checked : Scalar.distance (sourceCoefficient 48 64 3 2) v3543_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3543_upper : Scalar.QComplex := ((999995356486910300451164678471 : Int)/10^30,(-3047458714598982628782220352 : Int)/10^30)
theorem v3543_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 64 5) 1) 14) v3543_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3543 : Material (48 : Basis) (64 : Basis) where
  plus := ![v3543_pa,v3543_pb,v3543_pg]
  minus := ![(Primitive.Addresses.material3543 1).one,v3543_mb,v3543_mg]
  upper := v3543_upper
  lower := (Primitive.Addresses.material3543 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3543_pa_checked.trans (by decide +kernel)
    · exact v3543_pb_checked.trans (by decide +kernel)
    · exact v3543_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 64 Primitive.Addresses.material3543
    · exact v3543_mb_checked.trans (by decide +kernel)
    · exact v3543_mg_checked.trans (by decide +kernel)
  upper_error := v3543_upper_checked
  lower_error := reuse_lower_error 48 64 Primitive.Addresses.material3543

def v3544_pa : Scalar.QComplex := ((999999078569984547295526473140 : Int)/10^30,(-1357519495945504117415469633 : Int)/10^30)
theorem v3544_pa_checked : Scalar.distance (sourceCoefficient 48 65 1 0) v3544_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3544_pb : Scalar.QComplex := ((-585739140658392956660450 : Int)/10^30,(-431477118884988193902341321 : Int)/10^30)
theorem v3544_pb_checked : Scalar.distance (sourceCoefficient 48 65 1 1) v3544_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3544_pg : Scalar.QComplex := ((-93086343634691249923012 : Int)/10^30,(126366642728393613188 : Int)/10^30)
theorem v3544_pg_checked : Scalar.distance (sourceCoefficient 48 65 1 2) v3544_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3544_mb : Scalar.QComplex := ((-958084243150638687656438 : Int)/10^30,(-431476452759839677930275977 : Int)/10^30)
theorem v3544_mb_checked : Scalar.distance (sourceCoefficient 48 65 3 1) v3544_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3544_mg : Scalar.QComplex := ((-93086199925669926371082 : Int)/10^30,(206695917779769708210 : Int)/10^30)
theorem v3544_mg_checked : Scalar.distance (sourceCoefficient 48 65 3 2) v3544_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3544_upper : Scalar.QComplex := ((999995246233328365471405388005 : Int)/10^30,(-3083425164483725368884287544 : Int)/10^30)
theorem v3544_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 65 5) 1) 14) v3544_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3544 : Material (48 : Basis) (65 : Basis) where
  plus := ![v3544_pa,v3544_pb,v3544_pg]
  minus := ![(Primitive.Addresses.material3544 1).one,v3544_mb,v3544_mg]
  upper := v3544_upper
  lower := (Primitive.Addresses.material3544 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3544_pa_checked.trans (by decide +kernel)
    · exact v3544_pb_checked.trans (by decide +kernel)
    · exact v3544_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 65 Primitive.Addresses.material3544
    · exact v3544_mb_checked.trans (by decide +kernel)
    · exact v3544_mg_checked.trans (by decide +kernel)
  upper_error := v3544_upper_checked
  lower_error := reuse_lower_error 48 65 Primitive.Addresses.material3544

def v3545_pa : Scalar.QComplex := ((999999054539859005979391262446 : Int)/10^30,(-1375107046048838704386725585 : Int)/10^30)
theorem v3545_pa_checked : Scalar.distance (sourceCoefficient 48 66 1 0) v3545_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3545_pb : Scalar.QComplex := ((-593327772193110756022203 : Int)/10^30,(-431477107858757069982473066 : Int)/10^30)
theorem v3545_pb_checked : Scalar.distance (sourceCoefficient 48 66 1 1) v3545_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3545_pg : Scalar.QComplex := ((-93086341326859178924295 : Int)/10^30,(128003804871966664316 : Int)/10^30)
theorem v3545_pg_checked : Scalar.distance (sourceCoefficient 48 66 1 2) v3545_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3545_mb : Scalar.QComplex := ((-965672862344621292120685 : Int)/10^30,(-431476435184965424395598519 : Int)/10^30)
theorem v3545_mb_checked : Scalar.distance (sourceCoefficient 48 66 3 1) v3545_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3545_mg : Scalar.QComplex := ((-93086196205041519825947 : Int)/10^30,(208333077322197334905 : Int)/10^30)
theorem v3545_mg_checked : Scalar.distance (sourceCoefficient 48 66 3 2) v3545_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3545_upper : Scalar.QComplex := ((999995191848722665930767517003 : Int)/10^30,(-3101012646918653367349171404 : Int)/10^30)
theorem v3545_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 66 5) 1) 14) v3545_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3545 : Material (48 : Basis) (66 : Basis) where
  plus := ![v3545_pa,v3545_pb,v3545_pg]
  minus := ![(Primitive.Addresses.material3545 1).one,v3545_mb,v3545_mg]
  upper := v3545_upper
  lower := (Primitive.Addresses.material3545 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3545_pa_checked.trans (by decide +kernel)
    · exact v3545_pb_checked.trans (by decide +kernel)
    · exact v3545_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 66 Primitive.Addresses.material3545
    · exact v3545_mb_checked.trans (by decide +kernel)
    · exact v3545_mg_checked.trans (by decide +kernel)
  upper_error := v3545_upper_checked
  lower_error := reuse_lower_error 48 66 Primitive.Addresses.material3545

def v3546_pa : Scalar.QComplex := ((999999013514980387590689634619 : Int)/10^30,(-1404624172535886804014079844 : Int)/10^30)
theorem v3546_pa_checked : Scalar.distance (sourceCoefficient 48 67 1 0) v3546_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3546_pb : Scalar.QComplex := ((-606063746912338500837967 : Int)/10^30,(-431477088953519990715956443 : Int)/10^30)
theorem v3546_pb_checked : Scalar.distance (sourceCoefficient 48 67 1 1) v3546_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3546_pg : Scalar.QComplex := ((-93086337378133133874509 : Int)/10^30,(130751448598501978953 : Int)/10^30)
theorem v3546_pg_checked : Scalar.distance (sourceCoefficient 48 67 1 2) v3546_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3546_mb : Scalar.QComplex := ((-978408816007295447032162 : Int)/10^30,(-431476405289162808727375727 : Int)/10^30)
theorem v3546_mb_checked : Scalar.distance (sourceCoefficient 48 67 3 1) v3546_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3546_mg : Scalar.QComplex := ((-93086189885224158347011 : Int)/10^30,(211080716618086583773 : Int)/10^30)
theorem v3546_mg_checked : Scalar.distance (sourceCoefficient 48 67 3 2) v3546_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3546_upper : Scalar.QComplex := ((999995099880022605431919091160 : Int)/10^30,(-3130529658638190142338525783 : Int)/10^30)
theorem v3546_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 67 5) 1) 14) v3546_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3546 : Material (48 : Basis) (67 : Basis) where
  plus := ![v3546_pa,v3546_pb,v3546_pg]
  minus := ![(Primitive.Addresses.material3546 1).one,v3546_mb,v3546_mg]
  upper := v3546_upper
  lower := (Primitive.Addresses.material3546 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3546_pa_checked.trans (by decide +kernel)
    · exact v3546_pb_checked.trans (by decide +kernel)
    · exact v3546_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 67 Primitive.Addresses.material3546
    · exact v3546_mb_checked.trans (by decide +kernel)
    · exact v3546_mg_checked.trans (by decide +kernel)
  upper_error := v3546_upper_checked
  lower_error := reuse_lower_error 48 67 Primitive.Addresses.material3546

def v3547_pa : Scalar.QComplex := ((999998943258236670146812306048 : Int)/10^30,(-1453782105391503300540069922 : Int)/10^30)
theorem v3547_pa_checked : Scalar.distance (sourceCoefficient 48 68 1 0) v3547_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3547_pb : Scalar.QComplex := ((-627274286284537969553365 : Int)/10^30,(-431477056356170994472940074 : Int)/10^30)
theorem v3547_pb_checked : Scalar.distance (sourceCoefficient 48 68 1 1) v3547_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3547_pg : Scalar.QComplex := ((-93086330591902413203314 : Int)/10^30,(135327384677164502447 : Int)/10^30)
theorem v3547_pg_checked : Scalar.distance (sourceCoefficient 48 68 1 2) v3547_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3547_mb : Scalar.QComplex := ((-999619319351797684282078 : Int)/10^30,(-431476354388085758990416536 : Int)/10^30)
theorem v3547_mb_checked : Scalar.distance (sourceCoefficient 48 68 3 1) v3547_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3547_mg : Scalar.QComplex := ((-93086179150169221124371 : Int)/10^30,(215656645136707503118 : Int)/10^30)
theorem v3547_mg_checked : Scalar.distance (sourceCoefficient 48 68 3 2) v3547_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3547_upper : Scalar.QComplex := ((999994944781250991193189357592 : Int)/10^30,(-3179687397022074132546970381 : Int)/10^30)
theorem v3547_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 68 5) 1) 14) v3547_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3547 : Material (48 : Basis) (68 : Basis) where
  plus := ![v3547_pa,v3547_pb,v3547_pg]
  minus := ![(Primitive.Addresses.material3547 1).one,v3547_mb,v3547_mg]
  upper := v3547_upper
  lower := (Primitive.Addresses.material3547 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3547_pa_checked.trans (by decide +kernel)
    · exact v3547_pb_checked.trans (by decide +kernel)
    · exact v3547_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 68 Primitive.Addresses.material3547
    · exact v3547_mb_checked.trans (by decide +kernel)
    · exact v3547_mg_checked.trans (by decide +kernel)
  upper_error := v3547_upper_checked
  lower_error := reuse_lower_error 48 68 Primitive.Addresses.material3547

def v3548_pa : Scalar.QComplex := ((999998911571052337164750242507 : Int)/10^30,(-1475417469954892593580987008 : Int)/10^30)
theorem v3548_pa_checked : Scalar.distance (sourceCoefficient 48 69 1 0) v3548_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3548_pb : Scalar.QComplex := ((-636609457919315733473251 : Int)/10^30,(-431477041568862668014190432 : Int)/10^30)
theorem v3548_pb_checked : Scalar.distance (sourceCoefficient 48 69 1 1) v3548_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3548_pg : Scalar.QComplex := ((-93086327521981123301170 : Int)/10^30,(137341343326167662622 : Int)/10^30)
theorem v3548_pg_checked : Scalar.distance (sourceCoefficient 48 69 1 2) v3548_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3548_mb : Scalar.QComplex := ((-1008954474749883320064329 : Int)/10^30,(-431476331544950258232104489 : Int)/10^30)
theorem v3548_mb_checked : Scalar.distance (sourceCoefficient 48 69 3 1) v3548_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3548_mg : Scalar.QComplex := ((-93086174342293465534909 : Int)/10^30,(217670600386618006748 : Int)/10^30)
theorem v3548_mg_checked : Scalar.distance (sourceCoefficient 48 69 3 2) v3548_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3548_upper : Scalar.QComplex := ((999994875753437361081101936719 : Int)/10^30,(-3201322674672923857049774785 : Int)/10^30)
theorem v3548_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 69 5) 1) 14) v3548_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3548 : Material (48 : Basis) (69 : Basis) where
  plus := ![v3548_pa,v3548_pb,v3548_pg]
  minus := ![(Primitive.Addresses.material3548 1).one,v3548_mb,v3548_mg]
  upper := v3548_upper
  lower := (Primitive.Addresses.material3548 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3548_pa_checked.trans (by decide +kernel)
    · exact v3548_pb_checked.trans (by decide +kernel)
    · exact v3548_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 69 Primitive.Addresses.material3548
    · exact v3548_mb_checked.trans (by decide +kernel)
    · exact v3548_mg_checked.trans (by decide +kernel)
  upper_error := v3548_upper_checked
  lower_error := reuse_lower_error 48 69 Primitive.Addresses.material3548

def v3549_pa : Scalar.QComplex := ((999998890471686506743313004127 : Int)/10^30,(-1489649420479004828723999752 : Int)/10^30)
theorem v3549_pa_checked : Scalar.distance (sourceCoefficient 48 70 1 0) v3549_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3549_pb : Scalar.QComplex := ((-642750223363721956377836 : Int)/10^30,(-431477031694793697531918930 : Int)/10^30)
theorem v3549_pb_checked : Scalar.distance (sourceCoefficient 48 70 1 1) v3549_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3549_pg : Scalar.QComplex := ((-93086325474839054593319 : Int)/10^30,(138666144652127636146 : Int)/10^30)
theorem v3549_pg_checked : Scalar.distance (sourceCoefficient 48 70 1 2) v3549_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3549_mb : Scalar.QComplex := ((-1015095229386925111203194 : Int)/10^30,(-431476316371680955603269735 : Int)/10^30)
theorem v3549_mb_checked : Scalar.distance (sourceCoefficient 48 70 3 1) v3549_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3549_mg : Scalar.QComplex := ((-93086171151908281604937 : Int)/10^30,(218995399452702494767 : Int)/10^30)
theorem v3549_mg_checked : Scalar.distance (sourceCoefficient 48 70 3 2) v3549_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3549_upper : Scalar.QComplex := ((999994830091047463534775998830 : Int)/10^30,(-3215554567584626285082339164 : Int)/10^30)
theorem v3549_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 70 5) 1) 14) v3549_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3549 : Material (48 : Basis) (70 : Basis) where
  plus := ![v3549_pa,v3549_pb,v3549_pg]
  minus := ![(Primitive.Addresses.material3549 1).one,v3549_mb,v3549_mg]
  upper := v3549_upper
  lower := (Primitive.Addresses.material3549 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3549_pa_checked.trans (by decide +kernel)
    · exact v3549_pb_checked.trans (by decide +kernel)
    · exact v3549_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 70 Primitive.Addresses.material3549
    · exact v3549_mb_checked.trans (by decide +kernel)
    · exact v3549_mg_checked.trans (by decide +kernel)
  upper_error := v3549_upper_checked
  lower_error := reuse_lower_error 48 70 Primitive.Addresses.material3549

def v3550_pa : Scalar.QComplex := ((999998853988836338750653414425 : Int)/10^30,(-1513942209590878490927647456 : Int)/10^30)
theorem v3550_pa_checked : Scalar.distance (sourceCoefficient 48 71 1 0) v3550_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3550_pb : Scalar.QComplex := ((-653232013439004970251845 : Int)/10^30,(-431477014571349877065883436 : Int)/10^30)
theorem v3550_pb_checked : Scalar.distance (sourceCoefficient 48 71 1 1) v3550_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3550_pg : Scalar.QComplex := ((-93086321929714559268606 : Int)/10^30,(140927473409417701793 : Int)/10^30)
theorem v3550_pg_checked : Scalar.distance (sourceCoefficient 48 71 1 2) v3550_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3550_mb : Scalar.QComplex := ((-1025577000782597832796545 : Int)/10^30,(-431476290202930758309179676 : Int)/10^30)
theorem v3550_mb_checked : Scalar.distance (sourceCoefficient 48 71 3 1) v3550_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3550_mg : Scalar.QComplex := ((-93086165655360235217277 : Int)/10^30,(221256724308713743260 : Int)/10^30)
theorem v3550_mg_checked : Scalar.distance (sourceCoefficient 48 71 3 2) v3550_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3550_upper : Scalar.QComplex := ((999994751681101449980820097105 : Int)/10^30,(-3239847257549154504973890403 : Int)/10^30)
theorem v3550_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 71 5) 1) 14) v3550_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3550 : Material (48 : Basis) (71 : Basis) where
  plus := ![v3550_pa,v3550_pb,v3550_pg]
  minus := ![(Primitive.Addresses.material3550 1).one,v3550_mb,v3550_mg]
  upper := v3550_upper
  lower := (Primitive.Addresses.material3550 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3550_pa_checked.trans (by decide +kernel)
    · exact v3550_pb_checked.trans (by decide +kernel)
    · exact v3550_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 71 Primitive.Addresses.material3550
    · exact v3550_mb_checked.trans (by decide +kernel)
    · exact v3550_mg_checked.trans (by decide +kernel)
  upper_error := v3550_upper_checked
  lower_error := reuse_lower_error 48 71 Primitive.Addresses.material3550

def v3551_pa : Scalar.QComplex := ((999998813729850194279596844232 : Int)/10^30,(-1540304805022230814642143058 : Int)/10^30)
theorem v3551_pa_checked : Scalar.distance (sourceCoefficient 48 72 1 0) v3551_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3551_pb : Scalar.QComplex := ((-664606877989949605926183 : Int)/10^30,(-431476995604812649899435185 : Int)/10^30)
theorem v3551_pb_checked : Scalar.distance (sourceCoefficient 48 72 1 1) v3551_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3551_pg : Scalar.QComplex := ((-93086318010023202714106 : Int)/10^30,(143381473001827619226 : Int)/10^30)
theorem v3551_pg_checked : Scalar.distance (sourceCoefficient 48 72 1 2) v3551_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3551_mb : Scalar.QComplex := ((-1036951844730893133244648 : Int)/10^30,(-431476261420404790667857489 : Int)/10^30)
theorem v3551_mb_checked : Scalar.distance (sourceCoefficient 48 72 3 1) v3551_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3551_mg : Scalar.QComplex := ((-93086159617979213932045 : Int)/10^30,(223710719604870354756 : Int)/10^30)
theorem v3551_mg_checked : Scalar.distance (sourceCoefficient 48 72 3 2) v3551_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3551_upper : Scalar.QComplex := ((999994665922727148001772035677 : Int)/10^30,(-3266209744233159883020594460 : Int)/10^30)
theorem v3551_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 72 5) 1) 14) v3551_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3551 : Material (48 : Basis) (72 : Basis) where
  plus := ![v3551_pa,v3551_pb,v3551_pg]
  minus := ![(Primitive.Addresses.material3551 1).one,v3551_mb,v3551_mg]
  upper := v3551_upper
  lower := (Primitive.Addresses.material3551 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3551_pa_checked.trans (by decide +kernel)
    · exact v3551_pb_checked.trans (by decide +kernel)
    · exact v3551_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 72 Primitive.Addresses.material3551
    · exact v3551_mb_checked.trans (by decide +kernel)
    · exact v3551_mg_checked.trans (by decide +kernel)
  upper_error := v3551_upper_checked
  lower_error := reuse_lower_error 48 72 Primitive.Addresses.material3551

def v3552_pa : Scalar.QComplex := ((999998799129872425458673008671 : Int)/10^30,(-1549754436373717677472042712 : Int)/10^30)
theorem v3552_pa_checked : Scalar.distance (sourceCoefficient 48 73 1 0) v3552_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3552_pb : Scalar.QComplex := ((-668684180447712000548844 : Int)/10^30,(-431476988708941718508740523 : Int)/10^30)
theorem v3552_pb_checked : Scalar.distance (sourceCoefficient 48 73 1 1) v3552_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3552_pg : Scalar.QComplex := ((-93086316586639941087137 : Int)/10^30,(144261105334685596382 : Int)/10^30)
theorem v3552_pg_checked : Scalar.distance (sourceCoefficient 48 73 1 2) v3552_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3552_mb : Scalar.QComplex := ((-1041029139719663445621936 : Int)/10^30,(-431476251006008040761971122 : Int)/10^30)
theorem v3552_mb_checked : Scalar.distance (sourceCoefficient 48 73 3 1) v3552_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3552_mg : Scalar.QComplex := ((-93086157435513396208895 : Int)/10^30,(224590350381885365223 : Int)/10^30)
theorem v3552_mg_checked : Scalar.distance (sourceCoefficient 48 73 3 2) v3552_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3552_upper : Scalar.QComplex := ((999994635013564675326004865379 : Int)/10^30,(-3275659336312293750136679304 : Int)/10^30)
theorem v3552_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 48 73 5) 1) 14) v3552_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3552 : Material (48 : Basis) (73 : Basis) where
  plus := ![v3552_pa,v3552_pb,v3552_pg]
  minus := ![(Primitive.Addresses.material3552 1).one,v3552_mb,v3552_mg]
  upper := v3552_upper
  lower := (Primitive.Addresses.material3552 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3552_pa_checked.trans (by decide +kernel)
    · exact v3552_pb_checked.trans (by decide +kernel)
    · exact v3552_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 48 73 Primitive.Addresses.material3552
    · exact v3552_mb_checked.trans (by decide +kernel)
    · exact v3552_mg_checked.trans (by decide +kernel)
  upper_error := v3552_upper_checked
  lower_error := reuse_lower_error 48 73 Primitive.Addresses.material3552

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
