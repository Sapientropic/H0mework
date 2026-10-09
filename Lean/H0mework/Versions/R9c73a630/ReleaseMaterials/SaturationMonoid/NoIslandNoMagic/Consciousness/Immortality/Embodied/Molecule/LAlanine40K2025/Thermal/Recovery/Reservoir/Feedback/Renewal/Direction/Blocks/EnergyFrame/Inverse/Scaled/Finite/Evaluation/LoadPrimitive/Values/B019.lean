import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B012
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B013

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v305_pa : Scalar.QComplex := ((999992315424672456171563887089 : Int)/10^30,(3920343301598686800506977176 : Int)/10^30)
theorem v305_pa_checked : Scalar.distance (sourceCoefficient 3 21 1 0) v305_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v305_pb : Scalar.QComplex := ((1691534947070908267153769 : Int)/10^30,(-431472914031125354623543490 : Int)/10^30)
theorem v305_pb_checked : Scalar.distance (sourceCoefficient 3 21 1 1) v305_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v305_pg : Scalar.QComplex := ((-93085575281123532706476 : Int)/10^30,(-364930215862546031002 : Int)/10^30)
theorem v305_pg_checked : Scalar.distance (sourceCoefficient 3 21 1 2) v305_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v305_mb : Scalar.QComplex := ((1319192625244947149659042 : Int)/10^30,(-431474213092515590769126819 : Int)/10^30)
theorem v305_mb_checked : Scalar.distance (sourceCoefficient 3 21 3 1) v305_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v305_mg : Scalar.QComplex := ((-93085855539450077173147 : Int)/10^30,(-284601420933419686796 : Int)/10^30)
theorem v305_mg_checked : Scalar.distance (sourceCoefficient 3 21 3 2) v305_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v305_upper : Scalar.QComplex := ((999997592210473773326640685564 : Int)/10^30,(2194441444879070841816444699 : Int)/10^30)
theorem v305_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 21 5) 1) 14) v305_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material305 : Material (3 : Basis) (21 : Basis) where
  plus := ![v305_pa,v305_pb,v305_pg]
  minus := ![(Primitive.Addresses.material305 1).one,v305_mb,v305_mg]
  upper := v305_upper
  lower := (Primitive.Addresses.material305 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v305_pa_checked.trans (by decide +kernel)
    · exact v305_pb_checked.trans (by decide +kernel)
    · exact v305_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 21 Primitive.Addresses.material305
    · exact v305_mb_checked.trans (by decide +kernel)
    · exact v305_mg_checked.trans (by decide +kernel)
  upper_error := v305_upper_checked
  lower_error := reuse_lower_error 3 21 Primitive.Addresses.material305

def v306_pa : Scalar.QComplex := ((999992320889043804587024986084 : Int)/10^30,(3918949214221300468420549287 : Int)/10^30)
theorem v306_pa_checked : Scalar.distance (sourceCoefficient 3 22 1 0) v306_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v306_pb : Scalar.QComplex := ((1690933428175155153301764 : Int)/10^30,(-431472915539102849440197891 : Int)/10^30)
theorem v306_pb_checked : Scalar.distance (sourceCoefficient 3 22 1 1) v306_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v306_pg : Scalar.QComplex := ((-93085575698117494273495 : Int)/10^30,(-364800445080569580133 : Int)/10^30)
theorem v306_pg_checked : Scalar.distance (sourceCoefficient 3 22 1 2) v306_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v306_mb : Scalar.QComplex := ((1318591105271850350225933 : Int)/10^30,(-431474214081408808467289149 : Int)/10^30)
theorem v306_mb_checked : Scalar.distance (sourceCoefficient 3 22 3 1) v306_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v306_mg : Scalar.QComplex := ((-93085855844457543287635 : Int)/10^30,(-284471649839915820753 : Int)/10^30)
theorem v306_mg_checked : Scalar.distance (sourceCoefficient 3 22 3 2) v306_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v306_upper : Scalar.QComplex := ((999997595268768640453001516577 : Int)/10^30,(2193047350147004673871287166 : Int)/10^30)
theorem v306_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 22 5) 1) 14) v306_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material306 : Material (3 : Basis) (22 : Basis) where
  plus := ![v306_pa,v306_pb,v306_pg]
  minus := ![(Primitive.Addresses.material306 1).one,v306_mb,v306_mg]
  upper := v306_upper
  lower := (Primitive.Addresses.material306 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v306_pa_checked.trans (by decide +kernel)
    · exact v306_pb_checked.trans (by decide +kernel)
    · exact v306_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 22 Primitive.Addresses.material306
    · exact v306_mb_checked.trans (by decide +kernel)
    · exact v306_mg_checked.trans (by decide +kernel)
  upper_error := v306_upper_checked
  lower_error := reuse_lower_error 3 22 Primitive.Addresses.material306

def v307_pa : Scalar.QComplex := ((999992361235364690681791837205 : Int)/10^30,(3908640546263301859525234789 : Int)/10^30)
theorem v307_pa_checked : Scalar.distance (sourceCoefficient 3 23 1 0) v307_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v307_pb : Scalar.QComplex := ((1686485458405023311609139 : Int)/10^30,(-431472926655235607835753457 : Int)/10^30)
theorem v307_pb_checked : Scalar.distance (sourceCoefficient 3 23 1 1) v307_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v307_pg : Scalar.QComplex := ((-93085578775054985698501 : Int)/10^30,(-363840846767159702443 : Int)/10^30)
theorem v307_pg_checked : Scalar.distance (sourceCoefficient 3 23 1 2) v307_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v307_mb : Scalar.QComplex := ((1314143127565179017753232 : Int)/10^30,(-431474221359139845316687194 : Int)/10^30)
theorem v307_mb_checked : Scalar.distance (sourceCoefficient 3 23 3 1) v307_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v307_mg : Scalar.QComplex := ((-93085858093303763259147 : Int)/10^30,(-283512049228549775976 : Int)/10^30)
theorem v307_mg_checked : Scalar.distance (sourceCoefficient 3 23 3 2) v307_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v307_upper : Scalar.QComplex := ((999997617823203734988428147577 : Int)/10^30,(2182738627908466387451960699 : Int)/10^30)
theorem v307_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 23 5) 1) 14) v307_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material307 : Material (3 : Basis) (23 : Basis) where
  plus := ![v307_pa,v307_pb,v307_pg]
  minus := ![(Primitive.Addresses.material307 1).one,v307_mb,v307_mg]
  upper := v307_upper
  lower := (Primitive.Addresses.material307 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v307_pa_checked.trans (by decide +kernel)
    · exact v307_pb_checked.trans (by decide +kernel)
    · exact v307_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 23 Primitive.Addresses.material307
    · exact v307_mb_checked.trans (by decide +kernel)
    · exact v307_mg_checked.trans (by decide +kernel)
  upper_error := v307_upper_checked
  lower_error := reuse_lower_error 3 23 Primitive.Addresses.material307

def v308_pa : Scalar.QComplex := ((999992559067137145503474681712 : Int)/10^30,(3857694954014265180105629596 : Int)/10^30)
theorem v308_pa_checked : Scalar.distance (sourceCoefficient 3 24 1 0) v308_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v308_pb : Scalar.QComplex := ((1664503525874404128661273 : Int)/10^30,(-431472980693657789108723947 : Int)/10^30)
theorem v308_pb_checked : Scalar.distance (sourceCoefficient 3 24 1 1) v308_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v308_pg : Scalar.QComplex := ((-93085593811871049933692 : Int)/10^30,(-359098497567288007498 : Int)/10^30)
theorem v308_pg_checked : Scalar.distance (sourceCoefficient 3 24 1 2) v308_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v308_mb : Scalar.QComplex := ((1292161156586713397650529 : Int)/10^30,(-431474256428124161180603724 : Int)/10^30)
theorem v308_mb_checked : Scalar.distance (sourceCoefficient 3 24 3 1) v308_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v308_mg : Scalar.QComplex := ((-93085869037680456590451 : Int)/10^30,(-278769688818376393828 : Int)/10^30)
theorem v308_mg_checked : Scalar.distance (sourceCoefficient 3 24 3 2) v308_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v308_upper : Scalar.QComplex := ((999997727727211068812401608340 : Int)/10^30,(2131792770097212774498818751 : Int)/10^30)
theorem v308_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 24 5) 1) 14) v308_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material308 : Material (3 : Basis) (24 : Basis) where
  plus := ![v308_pa,v308_pb,v308_pg]
  minus := ![(Primitive.Addresses.material308 1).one,v308_mb,v308_mg]
  upper := v308_upper
  lower := (Primitive.Addresses.material308 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v308_pa_checked.trans (by decide +kernel)
    · exact v308_pb_checked.trans (by decide +kernel)
    · exact v308_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 24 Primitive.Addresses.material308
    · exact v308_mb_checked.trans (by decide +kernel)
    · exact v308_mg_checked.trans (by decide +kernel)
  upper_error := v308_upper_checked
  lower_error := reuse_lower_error 3 24 Primitive.Addresses.material308

def v309_pa : Scalar.QComplex := ((999992647469568190636819091782 : Int)/10^30,(3834710784911291804764876108 : Int)/10^30)
theorem v309_pa_checked : Scalar.distance (sourceCoefficient 3 25 1 0) v309_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v309_pb : Scalar.QComplex := ((1654586349474249085900147 : Int)/10^30,(-431473004584369903570440099 : Int)/10^30)
theorem v309_pb_checked : Scalar.distance (sourceCoefficient 3 25 1 1) v309_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v309_pg : Scalar.QComplex := ((-93085600503479891116113 : Int)/10^30,(-356958980722406982020 : Int)/10^30)
theorem v309_pg_checked : Scalar.distance (sourceCoefficient 3 25 1 2) v309_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v309_mb : Scalar.QComplex := ((1282243963262567808969252 : Int)/10^30,(-431474271760750799749060872 : Int)/10^30)
theorem v309_mb_checked : Scalar.distance (sourceCoefficient 3 25 3 1) v309_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v309_mg : Scalar.QComplex := ((-93085873882980129310386 : Int)/10^30,(-276630166995578219384 : Int)/10^30)
theorem v309_mg_checked : Scalar.distance (sourceCoefficient 3 25 3 2) v309_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v309_upper : Scalar.QComplex := ((999997776460919684710193028341 : Int)/10^30,(2108808482651883189872704364 : Int)/10^30)
theorem v309_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 25 5) 1) 14) v309_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material309 : Material (3 : Basis) (25 : Basis) where
  plus := ![v309_pa,v309_pb,v309_pg]
  minus := ![(Primitive.Addresses.material309 1).one,v309_mb,v309_mg]
  upper := v309_upper
  lower := (Primitive.Addresses.material309 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v309_pa_checked.trans (by decide +kernel)
    · exact v309_pb_checked.trans (by decide +kernel)
    · exact v309_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 25 Primitive.Addresses.material309
    · exact v309_mb_checked.trans (by decide +kernel)
    · exact v309_mg_checked.trans (by decide +kernel)
  upper_error := v309_upper_checked
  lower_error := reuse_lower_error 3 25 Primitive.Addresses.material309

def v310_pa : Scalar.QComplex := ((999992675604452639126097839933 : Int)/10^30,(3827366907934437059270333982 : Int)/10^30)
theorem v310_pa_checked : Scalar.distance (sourceCoefficient 3 26 1 0) v310_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v310_pb : Scalar.QComplex := ((1651417624020277176825729 : Int)/10^30,(-431473012153835973166152294 : Int)/10^30)
theorem v310_pb_checked : Scalar.distance (sourceCoefficient 3 26 1 1) v310_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v310_pg : Scalar.QComplex := ((-93085602629481214270421 : Int)/10^30,(-356275364610905409346 : Int)/10^30)
theorem v310_pg_checked : Scalar.distance (sourceCoefficient 3 26 1 2) v310_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v310_mb : Scalar.QComplex := ((1279075232456348902351247 : Int)/10^30,(-431474276595746698205506738 : Int)/10^30)
theorem v310_mb_checked : Scalar.distance (sourceCoefficient 3 26 3 1) v310_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v310_mg : Scalar.QComplex := ((-93085875419050745558105 : Int)/10^30,(-275946549303974777484 : Int)/10^30)
theorem v310_mg_checked : Scalar.distance (sourceCoefficient 3 26 3 2) v310_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v310_upper : Scalar.QComplex := ((999997791920896798857777549796 : Int)/10^30,(2101464568054612347700772740 : Int)/10^30)
theorem v310_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 26 5) 1) 14) v310_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material310 : Material (3 : Basis) (26 : Basis) where
  plus := ![v310_pa,v310_pb,v310_pg]
  minus := ![(Primitive.Addresses.material310 1).one,v310_mb,v310_mg]
  upper := v310_upper
  lower := (Primitive.Addresses.material310 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v310_pa_checked.trans (by decide +kernel)
    · exact v310_pb_checked.trans (by decide +kernel)
    · exact v310_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 26 Primitive.Addresses.material310
    · exact v310_mb_checked.trans (by decide +kernel)
    · exact v310_mg_checked.trans (by decide +kernel)
  upper_error := v310_upper_checked
  lower_error := reuse_lower_error 3 26 Primitive.Addresses.material310

def v311_pa : Scalar.QComplex := ((999992694901685207416761650213 : Int)/10^30,(3822321711358657692553836675 : Int)/10^30)
theorem v311_pa_checked : Scalar.distance (sourceCoefficient 3 27 1 0) v311_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v311_pb : Scalar.QComplex := ((1649240729894617362233570 : Int)/10^30,(-431473017336030720355380068 : Int)/10^30)
theorem v311_pb_checked : Scalar.distance (sourceCoefficient 3 27 1 1) v311_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v311_pg : Scalar.QComplex := ((-93085604086636410250572 : Int)/10^30,(-355805724711086524348 : Int)/10^30)
theorem v311_pg_checked : Scalar.distance (sourceCoefficient 3 27 1 2) v311_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v311_mb : Scalar.QComplex := ((1276898334669245590281627 : Int)/10^30,(-431474279899377929054239680 : Int)/10^30)
theorem v311_mb_checked : Scalar.distance (sourceCoefficient 3 27 3 1) v311_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v311_mg : Scalar.QComplex := ((-93085876470927317224980 : Int)/10^30,(-275476908321564984495 : Int)/10^30)
theorem v311_mg_checked : Scalar.distance (sourceCoefficient 3 27 3 2) v311_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v311_upper : Scalar.QComplex := ((999997802510549033050180730822 : Int)/10^30,(2096419345687787848580158297 : Int)/10^30)
theorem v311_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 27 5) 1) 14) v311_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material311 : Material (3 : Basis) (27 : Basis) where
  plus := ![v311_pa,v311_pb,v311_pg]
  minus := ![(Primitive.Addresses.material311 1).one,v311_mb,v311_mg]
  upper := v311_upper
  lower := (Primitive.Addresses.material311 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v311_pa_checked.trans (by decide +kernel)
    · exact v311_pb_checked.trans (by decide +kernel)
    · exact v311_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 27 Primitive.Addresses.material311
    · exact v311_mb_checked.trans (by decide +kernel)
    · exact v311_mg_checked.trans (by decide +kernel)
  upper_error := v311_upper_checked
  lower_error := reuse_lower_error 3 27 Primitive.Addresses.material311

def v312_pa : Scalar.QComplex := ((999992720857321293359407609203 : Int)/10^30,(3815525176367618232190558462 : Int)/10^30)
theorem v312_pa_checked : Scalar.distance (sourceCoefficient 3 28 1 0) v312_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v312_pb : Scalar.QComplex := ((1646308170829182800317763 : Int)/10^30,(-431473024293968611916597005 : Int)/10^30)
theorem v312_pb_checked : Scalar.distance (sourceCoefficient 3 28 1 1) v312_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v312_pg : Scalar.QComplex := ((-93085606045243359999553 : Int)/10^30,(-355173058778434281945 : Int)/10^30)
theorem v312_pg_checked : Scalar.distance (sourceCoefficient 3 28 1 2) v312_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v312_mb : Scalar.QComplex := ((1273965770691349766469665 : Int)/10^30,(-431474284326646833944516963 : Int)/10^30)
theorem v312_mb_checked : Scalar.distance (sourceCoefficient 3 28 3 1) v312_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v312_mg : Scalar.QComplex := ((-93085877883571332032047 : Int)/10^30,(-274844240934293597830 : Int)/10^30)
theorem v312_mg_checked : Scalar.distance (sourceCoefficient 3 28 3 2) v312_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v312_upper : Scalar.QComplex := ((999997816735943643425684443760 : Int)/10^30,(2089622776022315672862160740 : Int)/10^30)
theorem v312_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 28 5) 1) 14) v312_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material312 : Material (3 : Basis) (28 : Basis) where
  plus := ![v312_pa,v312_pb,v312_pg]
  minus := ![(Primitive.Addresses.material312 1).one,v312_mb,v312_mg]
  upper := v312_upper
  lower := (Primitive.Addresses.material312 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v312_pa_checked.trans (by decide +kernel)
    · exact v312_pb_checked.trans (by decide +kernel)
    · exact v312_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 28 Primitive.Addresses.material312
    · exact v312_mb_checked.trans (by decide +kernel)
    · exact v312_mg_checked.trans (by decide +kernel)
  upper_error := v312_upper_checked
  lower_error := reuse_lower_error 3 28 Primitive.Addresses.material312

def v313_pa : Scalar.QComplex := ((999992773284646250805007147333 : Int)/10^30,(3801759919048490609376438573 : Int)/10^30)
theorem v313_pa_checked : Scalar.distance (sourceCoefficient 3 29 1 0) v313_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v313_pb : Scalar.QComplex := ((1640368757654980096560821 : Int)/10^30,(-431473038304702835778127053 : Int)/10^30)
theorem v313_pb_checked : Scalar.distance (sourceCoefficient 3 29 1 1) v313_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v313_pg : Scalar.QComplex := ((-93085609996708325621434 : Int)/10^30,(-353891698600237050950 : Int)/10^30)
theorem v313_pg_checked : Scalar.distance (sourceCoefficient 3 29 1 2) v313_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v313_mb : Scalar.QComplex := ((1268026347638029416912464 : Int)/10^30,(-431474293211929772871693258 : Int)/10^30)
theorem v313_mb_checked : Scalar.distance (sourceCoefficient 3 29 3 1) v313_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v313_mg : Scalar.QComplex := ((-93085880729278702878839 : Int)/10^30,(-273562877823269024274 : Int)/10^30)
theorem v313_mg_checked : Scalar.distance (sourceCoefficient 3 29 3 2) v313_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v313_upper : Scalar.QComplex := ((999997845405605158104130156240 : Int)/10^30,(2075857448720115139393105862 : Int)/10^30)
theorem v313_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 29 5) 1) 14) v313_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material313 : Material (3 : Basis) (29 : Basis) where
  plus := ![v313_pa,v313_pb,v313_pg]
  minus := ![(Primitive.Addresses.material313 1).one,v313_mb,v313_mg]
  upper := v313_upper
  lower := (Primitive.Addresses.material313 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v313_pa_checked.trans (by decide +kernel)
    · exact v313_pb_checked.trans (by decide +kernel)
    · exact v313_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 29 Primitive.Addresses.material313
    · exact v313_mb_checked.trans (by decide +kernel)
    · exact v313_mg_checked.trans (by decide +kernel)
  upper_error := v313_upper_checked
  lower_error := reuse_lower_error 3 29 Primitive.Addresses.material313

def v314_pa : Scalar.QComplex := ((999992793102152658198338828691 : Int)/10^30,(3796543659080851568766505834 : Int)/10^30)
theorem v314_pa_checked : Scalar.distance (sourceCoefficient 3 30 1 0) v314_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v314_pb : Scalar.QComplex := ((1638118053438330812091455 : Int)/10^30,(-431473043585503127540448750 : Int)/10^30)
theorem v314_pb_checked : Scalar.distance (sourceCoefficient 3 30 1 1) v314_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v314_pg : Scalar.QComplex := ((-93085611488715247207495 : Int)/10^30,(-353406135011059188149 : Int)/10^30)
theorem v314_pg_checked : Scalar.distance (sourceCoefficient 3 30 1 2) v314_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v314_mb : Scalar.QComplex := ((1265775639702327361191106 : Int)/10^30,(-431474296550471727337351855 : Int)/10^30)
theorem v314_mb_checked : Scalar.distance (sourceCoefficient 3 30 3 1) v314_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v314_mg : Scalar.QComplex := ((-93085881802265560434280 : Int)/10^30,(-273077313127353901246 : Int)/10^30)
theorem v314_mg_checked : Scalar.distance (sourceCoefficient 3 30 3 2) v314_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v314_upper : Scalar.QComplex := ((999997856220290560912320072898 : Int)/10^30,(2070641162318264346619250821 : Int)/10^30)
theorem v314_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 30 5) 1) 14) v314_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material314 : Material (3 : Basis) (30 : Basis) where
  plus := ![v314_pa,v314_pb,v314_pg]
  minus := ![(Primitive.Addresses.material314 1).one,v314_mb,v314_mg]
  upper := v314_upper
  lower := (Primitive.Addresses.material314 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v314_pa_checked.trans (by decide +kernel)
    · exact v314_pb_checked.trans (by decide +kernel)
    · exact v314_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 30 Primitive.Addresses.material314
    · exact v314_mb_checked.trans (by decide +kernel)
    · exact v314_mg_checked.trans (by decide +kernel)
  upper_error := v314_upper_checked
  lower_error := reuse_lower_error 3 30 Primitive.Addresses.material314

def v315_pa : Scalar.QComplex := ((999992835163518530978840413508 : Int)/10^30,(3785448669319957392174510247 : Int)/10^30)
theorem v315_pa_checked : Scalar.distance (sourceCoefficient 3 31 1 0) v315_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v315_pb : Scalar.QComplex := ((1633330803558409356330104 : Int)/10^30,(-431473054765712032570430092 : Int)/10^30)
theorem v315_pb_checked : Scalar.distance (sourceCoefficient 3 31 1 1) v315_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v315_pg : Scalar.QComplex := ((-93085614652388231052206 : Int)/10^30,(-352373340816080733593 : Int)/10^30)
theorem v315_pg_checked : Scalar.distance (sourceCoefficient 3 31 1 2) v315_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v315_mb : Scalar.QComplex := ((1260988381956901076728381 : Int)/10^30,(-431474303599495432823162977 : Int)/10^30)
theorem v315_mb_checked : Scalar.distance (sourceCoefficient 3 31 3 1) v315_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v315_mg : Scalar.QComplex := ((-93085884074682491356358 : Int)/10^30,(-272044516586824627990 : Int)/10^30)
theorem v315_mg_checked : Scalar.distance (sourceCoefficient 3 31 3 2) v315_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v315_upper : Scalar.QComplex := ((999997879132647990534410969818 : Int)/10^30,(2059546116487952390714965677 : Int)/10^30)
theorem v315_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 31 5) 1) 14) v315_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material315 : Material (3 : Basis) (31 : Basis) where
  plus := ![v315_pa,v315_pb,v315_pg]
  minus := ![(Primitive.Addresses.material315 1).one,v315_mb,v315_mg]
  upper := v315_upper
  lower := (Primitive.Addresses.material315 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v315_pa_checked.trans (by decide +kernel)
    · exact v315_pb_checked.trans (by decide +kernel)
    · exact v315_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 31 Primitive.Addresses.material315
    · exact v315_mb_checked.trans (by decide +kernel)
    · exact v315_mg_checked.trans (by decide +kernel)
  upper_error := v315_upper_checked
  lower_error := reuse_lower_error 3 31 Primitive.Addresses.material315

def v316_pa : Scalar.QComplex := ((999992853231756882802009522860 : Int)/10^30,(3780672613429794869319560692 : Int)/10^30)
theorem v316_pa_checked : Scalar.distance (sourceCoefficient 3 32 1 0) v316_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v316_pb : Scalar.QComplex := ((1631270038007483578725778 : Int)/10^30,(-431473059556647490918439492 : Int)/10^30)
theorem v316_pb_checked : Scalar.distance (sourceCoefficient 3 32 1 1) v316_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v316_pg : Scalar.QComplex := ((-93085616010137191390021 : Int)/10^30,(-351928754307012851184 : Int)/10^30)
theorem v316_pg_checked : Scalar.distance (sourceCoefficient 3 32 1 2) v316_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v316_mb : Scalar.QComplex := ((1258927613038930970540807 : Int)/10^30,(-431474306612081250273015632 : Int)/10^30)
theorem v316_mb_checked : Scalar.distance (sourceCoefficient 3 32 3 1) v316_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v316_mg : Scalar.QComplex := ((-93085885048772812249665 : Int)/10^30,(-271599929071620419486 : Int)/10^30)
theorem v316_mg_checked : Scalar.distance (sourceCoefficient 3 32 3 2) v316_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v316_upper : Scalar.QComplex := ((999997888957820245824239717071 : Int)/10^30,(2054770036527023823853926584 : Int)/10^30)
theorem v316_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 32 5) 1) 14) v316_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material316 : Material (3 : Basis) (32 : Basis) where
  plus := ![v316_pa,v316_pb,v316_pg]
  minus := ![(Primitive.Addresses.material316 1).one,v316_mb,v316_mg]
  upper := v316_upper
  lower := (Primitive.Addresses.material316 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v316_pa_checked.trans (by decide +kernel)
    · exact v316_pb_checked.trans (by decide +kernel)
    · exact v316_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 32 Primitive.Addresses.material316
    · exact v316_mb_checked.trans (by decide +kernel)
    · exact v316_mg_checked.trans (by decide +kernel)
  upper_error := v316_upper_checked
  lower_error := reuse_lower_error 3 32 Primitive.Addresses.material316

def v317_pa : Scalar.QComplex := ((999992878374206572364764529627 : Int)/10^30,(3774016543326397351464804582 : Int)/10^30)
theorem v317_pa_checked : Scalar.distance (sourceCoefficient 3 33 1 0) v317_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v317_pb : Scalar.QComplex := ((1628398086724030841427419 : Int)/10^30,(-431473066211565568465568260 : Int)/10^30)
theorem v317_pb_checked : Scalar.distance (sourceCoefficient 3 33 1 1) v317_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v317_pg : Scalar.QComplex := ((-93085617898209268561130 : Int)/10^30,(-351309163786003854666 : Int)/10^30)
theorem v317_pg_checked : Scalar.distance (sourceCoefficient 3 33 1 2) v317_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v317_mb : Scalar.QComplex := ((1256055657081942376190342 : Int)/10^30,(-431474310788632240154474608 : Int)/10^30)
theorem v317_mb_checked : Scalar.distance (sourceCoefficient 3 33 3 1) v317_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v317_mg : Scalar.QComplex := ((-93085886402165472095658 : Int)/10^30,(-270980337151992123636 : Int)/10^30)
theorem v317_mg_checked : Scalar.distance (sourceCoefficient 3 33 3 2) v317_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v317_upper : Scalar.QComplex := ((999997902612459324160394071344 : Int)/10^30,(2048113932943473589124638590 : Int)/10^30)
theorem v317_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 33 5) 1) 14) v317_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material317 : Material (3 : Basis) (33 : Basis) where
  plus := ![v317_pa,v317_pb,v317_pg]
  minus := ![(Primitive.Addresses.material317 1).one,v317_mb,v317_mg]
  upper := v317_upper
  lower := (Primitive.Addresses.material317 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v317_pa_checked.trans (by decide +kernel)
    · exact v317_pb_checked.trans (by decide +kernel)
    · exact v317_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 33 Primitive.Addresses.material317
    · exact v317_mb_checked.trans (by decide +kernel)
    · exact v317_mg_checked.trans (by decide +kernel)
  upper_error := v317_upper_checked
  lower_error := reuse_lower_error 3 33 Primitive.Addresses.material317

def v318_pa : Scalar.QComplex := ((999992939257916324572026986602 : Int)/10^30,(3757849692746116709801307177 : Int)/10^30)
theorem v318_pa_checked : Scalar.distance (sourceCoefficient 3 34 1 0) v318_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v318_pb : Scalar.QComplex := ((1621422438080228884119921 : Int)/10^30,(-431473082269479882890777516 : Int)/10^30)
theorem v318_pb_checked : Scalar.distance (sourceCoefficient 3 34 1 1) v318_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v318_pg : Scalar.QComplex := ((-93085622464089506255125 : Int)/10^30,(-349804247653332224808 : Int)/10^30)
theorem v318_pg_checked : Scalar.distance (sourceCoefficient 3 34 1 2) v318_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v318_mb : Scalar.QComplex := ((1249079997178236380127034 : Int)/10^30,(-431474320826869967435533120 : Int)/10^30)
theorem v318_mb_checked : Scalar.distance (sourceCoefficient 3 34 3 1) v318_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v318_mg : Scalar.QComplex := ((-93085889669369166114698 : Int)/10^30,(-269475417639520542520 : Int)/10^30)
theorem v318_mg_checked : Scalar.distance (sourceCoefficient 3 34 3 2) v318_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v318_upper : Scalar.QComplex := ((999997935593560940897335316571 : Int)/10^30,(2031947001362058089809205664 : Int)/10^30)
theorem v318_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 34 5) 1) 14) v318_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material318 : Material (3 : Basis) (34 : Basis) where
  plus := ![v318_pa,v318_pb,v318_pg]
  minus := ![(Primitive.Addresses.material318 1).one,v318_mb,v318_mg]
  upper := v318_upper
  lower := (Primitive.Addresses.material318 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v318_pa_checked.trans (by decide +kernel)
    · exact v318_pb_checked.trans (by decide +kernel)
    · exact v318_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 34 Primitive.Addresses.material318
    · exact v318_mb_checked.trans (by decide +kernel)
    · exact v318_mg_checked.trans (by decide +kernel)
  upper_error := v318_upper_checked
  lower_error := reuse_lower_error 3 34 Primitive.Addresses.material318

def v319_pa : Scalar.QComplex := ((999993130949959780351467413084 : Int)/10^30,(3706487946370639692818433678 : Int)/10^30)
theorem v319_pa_checked : Scalar.distance (sourceCoefficient 3 35 1 0) v319_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v319_pb : Scalar.QComplex := ((1599260949409643831510103 : Int)/10^30,(-431473132287433020636733837 : Int)/10^30)
theorem v319_pb_checked : Scalar.distance (sourceCoefficient 3 35 1 1) v319_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v319_pg : Scalar.QComplex := ((-93085636781457076581820 : Int)/10^30,(-345023160692061951008 : Int)/10^30)
theorem v319_pg_checked : Scalar.distance (sourceCoefficient 3 35 1 2) v319_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v319_mb : Scalar.QComplex := ((1226918473596145556752579 : Int)/10^30,(-431474351720437874894603296 : Int)/10^30)
theorem v319_mb_checked : Scalar.distance (sourceCoefficient 3 35 3 1) v319_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v319_mg : Scalar.QComplex := ((-93085899860868690018094 : Int)/10^30,(-264694320103224067975 : Int)/10^30)
theorem v319_mg_checked : Scalar.distance (sourceCoefficient 3 35 3 2) v319_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v319_upper : Scalar.QComplex := ((999998038639604151055603362334 : Int)/10^30,(1980585000640792086211108727 : Int)/10^30)
theorem v319_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 35 5) 1) 14) v319_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material319 : Material (3 : Basis) (35 : Basis) where
  plus := ![v319_pa,v319_pb,v319_pg]
  minus := ![(Primitive.Addresses.material319 1).one,v319_mb,v319_mg]
  upper := v319_upper
  lower := (Primitive.Addresses.material319 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v319_pa_checked.trans (by decide +kernel)
    · exact v319_pb_checked.trans (by decide +kernel)
    · exact v319_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 35 Primitive.Addresses.material319
    · exact v319_mb_checked.trans (by decide +kernel)
    · exact v319_mg_checked.trans (by decide +kernel)
  upper_error := v319_upper_checked
  lower_error := reuse_lower_error 3 35 Primitive.Addresses.material319

def v320_pa : Scalar.QComplex := ((999993190660598801334699809128 : Int)/10^30,(3690343132459941032330606103 : Int)/10^30)
theorem v320_pa_checked : Scalar.distance (sourceCoefficient 3 36 1 0) v320_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v320_pb : Scalar.QComplex := ((1592294809917826176732886 : Int)/10^30,(-431473147696333641141046797 : Int)/10^30)
theorem v320_pb_checked : Scalar.distance (sourceCoefficient 3 36 1 1) v320_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v320_pg : Scalar.QComplex := ((-93085641222730090871916 : Int)/10^30,(-343520295963218392828 : Int)/10^30)
theorem v320_pg_checked : Scalar.distance (sourceCoefficient 3 36 1 2) v320_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v320_mb : Scalar.QComplex := ((1219952323400952758708129 : Int)/10^30,(-431474361117868119798371225 : Int)/10^30)
theorem v320_mb_checked : Scalar.distance (sourceCoefficient 3 36 3 1) v320_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v320_mg : Scalar.QComplex := ((-93085903005235476142025 : Int)/10^30,(-263191452101347148833 : Int)/10^30)
theorem v320_mg_checked : Scalar.distance (sourceCoefficient 3 36 3 2) v320_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v320_upper : Scalar.QComplex := ((999998070485670076267021679764 : Int)/10^30,(1964440107720751199285281434 : Int)/10^30)
theorem v320_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 36 5) 1) 14) v320_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material320 : Material (3 : Basis) (36 : Basis) where
  plus := ![v320_pa,v320_pb,v320_pg]
  minus := ![(Primitive.Addresses.material320 1).one,v320_mb,v320_mg]
  upper := v320_upper
  lower := (Primitive.Addresses.material320 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v320_pa_checked.trans (by decide +kernel)
    · exact v320_pb_checked.trans (by decide +kernel)
    · exact v320_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 36 Primitive.Addresses.material320
    · exact v320_mb_checked.trans (by decide +kernel)
    · exact v320_mg_checked.trans (by decide +kernel)
  upper_error := v320_upper_checked
  lower_error := reuse_lower_error 3 36 Primitive.Addresses.material320

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
