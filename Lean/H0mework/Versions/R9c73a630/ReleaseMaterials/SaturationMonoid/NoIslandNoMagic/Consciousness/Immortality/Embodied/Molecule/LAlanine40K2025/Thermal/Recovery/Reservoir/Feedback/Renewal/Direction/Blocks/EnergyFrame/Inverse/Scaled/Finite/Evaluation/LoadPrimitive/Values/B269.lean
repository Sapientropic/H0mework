import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B179
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B180

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4305_pa : Scalar.QComplex := ((999997827673359742817691069277 : Int)/10^30,(-2084382057472029921523420415 : Int)/10^30)
theorem v4305_pa_checked : Scalar.distance (sourceCoefficient 67 85 1 0) v4305_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4305_pb : Scalar.QComplex := ((-899363981170411229238020 : Int)/10^30,(-431476573229015179530656907 : Int)/10^30)
theorem v4305_pb_checked : Scalar.distance (sourceCoefficient 67 85 1 1) v4305_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4305_pg : Scalar.QComplex := ((-93086226554366388661797 : Int)/10^30,(194027681919200100171 : Int)/10^30)
theorem v4305_pg_checked : Scalar.distance (sourceCoefficient 67 85 1 2) v4305_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4305_mb : Scalar.QComplex := ((-1271708496009266195654551 : Int)/10^30,(-431475636459957612810159630 : Int)/10^30)
theorem v4305_mb_checked : Scalar.distance (sourceCoefficient 67 85 3 1) v4305_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4305_mg : Scalar.QComplex := ((-93086024456959177882222 : Int)/10^30,(274356830742231789020 : Int)/10^30)
theorem v4305_mg_checked : Scalar.distance (sourceCoefficient 67 85 3 2) v4305_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4305_upper : Scalar.QComplex := ((999992740839725886275146953267 : Int)/10^30,(-3810284484499755096369697340 : Int)/10^30)
theorem v4305_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 67 85 5) 1) 14) v4305_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4305 : Material (67 : Basis) (85 : Basis) where
  plus := ![v4305_pa,v4305_pb,v4305_pg]
  minus := ![(Primitive.Addresses.material4305 1).one,v4305_mb,v4305_mg]
  upper := v4305_upper
  lower := (Primitive.Addresses.material4305 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4305_pa_checked.trans (by decide +kernel)
    · exact v4305_pb_checked.trans (by decide +kernel)
    · exact v4305_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 67 85 Primitive.Addresses.material4305
    · exact v4305_mb_checked.trans (by decide +kernel)
    · exact v4305_mg_checked.trans (by decide +kernel)
  upper_error := v4305_upper_checked
  lower_error := reuse_lower_error 67 85 Primitive.Addresses.material4305

def v4306_pa : Scalar.QComplex := ((999997797167033575256606081717 : Int)/10^30,(-2098966669667817478991117903 : Int)/10^30)
theorem v4306_pa_checked : Scalar.distance (sourceCoefficient 67 86 1 0) v4306_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4306_pb : Scalar.QComplex := ((-905656911621403224479474 : Int)/10^30,(-431476559250857949850312879 : Int)/10^30)
theorem v4306_pb_checked : Scalar.distance (sourceCoefficient 67 86 1 1) v4306_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4306_pg : Scalar.QComplex := ((-93086223626688665348394 : Int)/10^30,(195385311198869078624 : Int)/10^30)
theorem v4306_pg_checked : Scalar.distance (sourceCoefficient 67 86 1 2) v4306_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4306_mb : Scalar.QComplex := ((-1278001412054592446479680 : Int)/10^30,(-431475617051290031696847568 : Int)/10^30)
theorem v4306_mb_checked : Scalar.distance (sourceCoefficient 67 86 3 1) v4306_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4306_mg : Scalar.QComplex := ((-93086020357709621675642 : Int)/10^30,(275714456989939322420 : Int)/10^30)
theorem v4306_mg_checked : Scalar.distance (sourceCoefficient 67 86 3 2) v4306_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4306_upper : Scalar.QComplex := ((999992685161727610056907008321 : Int)/10^30,(-3824869022322324564188980033 : Int)/10^30)
theorem v4306_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 67 86 5) 1) 14) v4306_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4306 : Material (67 : Basis) (86 : Basis) where
  plus := ![v4306_pa,v4306_pb,v4306_pg]
  minus := ![(Primitive.Addresses.material4306 1).one,v4306_mb,v4306_mg]
  upper := v4306_upper
  lower := (Primitive.Addresses.material4306 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4306_pa_checked.trans (by decide +kernel)
    · exact v4306_pb_checked.trans (by decide +kernel)
    · exact v4306_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 67 86 Primitive.Addresses.material4306
    · exact v4306_mb_checked.trans (by decide +kernel)
    · exact v4306_mg_checked.trans (by decide +kernel)
  upper_error := v4306_upper_checked
  lower_error := reuse_lower_error 67 86 Primitive.Addresses.material4306

def v4307_pa : Scalar.QComplex := ((999997795139476654083470123997 : Int)/10^30,(-2099932423979854083752808530 : Int)/10^30)
theorem v4307_pa_checked : Scalar.distance (sourceCoefficient 67 87 1 0) v4307_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4307_pb : Scalar.QComplex := ((-906073612771319709996843 : Int)/10^30,(-431476558320941548405801562 : Int)/10^30)
theorem v4307_pb_checked : Scalar.distance (sourceCoefficient 67 87 1 1) v4307_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4307_pg : Scalar.QComplex := ((-93086223432010137193100 : Int)/10^30,(195475209806284733965 : Int)/10^30)
theorem v4307_pg_checked : Scalar.distance (sourceCoefficient 67 87 1 2) v4307_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4307_mb : Scalar.QComplex := ((-1278418112246876077133167 : Int)/10^30,(-431475615761779651647893820 : Int)/10^30)
theorem v4307_mb_checked : Scalar.distance (sourceCoefficient 67 87 3 1) v4307_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4307_mg : Scalar.QComplex := ((-93086020085452716691327 : Int)/10^30,(275804355395882815848 : Int)/10^30)
theorem v4307_mg_checked : Scalar.distance (sourceCoefficient 67 87 3 2) v4307_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4307_upper : Scalar.QComplex := ((999992681467369378663248056091 : Int)/10^30,(-3825834771696604259224956592 : Int)/10^30)
theorem v4307_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 67 87 5) 1) 14) v4307_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4307 : Material (67 : Basis) (87 : Basis) where
  plus := ![v4307_pa,v4307_pb,v4307_pg]
  minus := ![(Primitive.Addresses.material4307 1).one,v4307_mb,v4307_mg]
  upper := v4307_upper
  lower := (Primitive.Addresses.material4307 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4307_pa_checked.trans (by decide +kernel)
    · exact v4307_pb_checked.trans (by decide +kernel)
    · exact v4307_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 67 87 Primitive.Addresses.material4307
    · exact v4307_mb_checked.trans (by decide +kernel)
    · exact v4307_mg_checked.trans (by decide +kernel)
  upper_error := v4307_upper_checked
  lower_error := reuse_lower_error 67 87 Primitive.Addresses.material4307

def v4308_pa : Scalar.QComplex := ((999997770375980986912548984805 : Int)/10^30,(-2111691991461564628992523701 : Int)/10^30)
theorem v4308_pa_checked : Scalar.distance (sourceCoefficient 67 88 1 0) v4308_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4308_pb : Scalar.QComplex := ((-911147600224327209980096 : Int)/10^30,(-431476546954710958778094861 : Int)/10^30)
theorem v4308_pb_checked : Scalar.distance (sourceCoefficient 67 88 1 1) v4308_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4308_pg : Scalar.QComplex := ((-93086221053369129217756 : Int)/10^30,(196569865790714661977 : Int)/10^30)
theorem v4308_pg_checked : Scalar.distance (sourceCoefficient 67 88 1 2) v4308_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4308_mb : Scalar.QComplex := ((-1283492088002061072853224 : Int)/10^30,(-431475600016930646153502650 : Int)/10^30)
theorem v4308_mb_checked : Scalar.distance (sourceCoefficient 67 88 3 1) v4308_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4308_mg : Scalar.QComplex := ((-93086016762173781305094 : Int)/10^30,(276899008920062232738 : Int)/10^30)
theorem v4308_mg_checked : Scalar.distance (sourceCoefficient 67 88 3 2) v4308_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4308_upper : Scalar.QComplex := ((999992636407963940006200717083 : Int)/10^30,(-3837594278924273421530587819 : Int)/10^30)
theorem v4308_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 67 88 5) 1) 14) v4308_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4308 : Material (67 : Basis) (88 : Basis) where
  plus := ![v4308_pa,v4308_pb,v4308_pg]
  minus := ![(Primitive.Addresses.material4308 1).one,v4308_mb,v4308_mg]
  upper := v4308_upper
  lower := (Primitive.Addresses.material4308 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4308_pa_checked.trans (by decide +kernel)
    · exact v4308_pb_checked.trans (by decide +kernel)
    · exact v4308_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 67 88 Primitive.Addresses.material4308
    · exact v4308_mb_checked.trans (by decide +kernel)
    · exact v4308_mg_checked.trans (by decide +kernel)
  upper_error := v4308_upper_checked
  lower_error := reuse_lower_error 67 88 Primitive.Addresses.material4308

def v4309_pa : Scalar.QComplex := ((999997736270509897557281797467 : Int)/10^30,(-2127781439841432839294485650 : Int)/10^30)
theorem v4309_pa_checked : Scalar.distance (sourceCoefficient 67 89 1 0) v4309_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4309_pb : Scalar.QComplex := ((-918089833280149578867668 : Int)/10^30,(-431476531274536085733168197 : Int)/10^30)
theorem v4309_pb_checked : Scalar.distance (sourceCoefficient 67 89 1 1) v4309_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4309_pg : Scalar.QComplex := ((-93086217774580033259063 : Int)/10^30,(198067574857199318625 : Int)/10^30)
theorem v4309_pg_checked : Scalar.distance (sourceCoefficient 67 89 1 2) v4309_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4309_mb : Scalar.QComplex := ((-1290434304941688092756544 : Int)/10^30,(-431475578345927150949701843 : Int)/10^30)
theorem v4309_mb_checked : Scalar.distance (sourceCoefficient 67 89 3 1) v4309_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4309_mg : Scalar.QComplex := ((-93086012190930436125503 : Int)/10^30,(278396714599434036615 : Int)/10^30)
theorem v4309_mg_checked : Scalar.distance (sourceCoefficient 67 89 3 2) v4309_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4309_upper : Scalar.QComplex := ((999992574533615366446349796154 : Int)/10^30,(-3853683644477849193331609218 : Int)/10^30)
theorem v4309_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 67 89 5) 1) 14) v4309_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4309 : Material (67 : Basis) (89 : Basis) where
  plus := ![v4309_pa,v4309_pb,v4309_pg]
  minus := ![(Primitive.Addresses.material4309 1).one,v4309_mb,v4309_mg]
  upper := v4309_upper
  lower := (Primitive.Addresses.material4309 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4309_pa_checked.trans (by decide +kernel)
    · exact v4309_pb_checked.trans (by decide +kernel)
    · exact v4309_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 67 89 Primitive.Addresses.material4309
    · exact v4309_mb_checked.trans (by decide +kernel)
    · exact v4309_mg_checked.trans (by decide +kernel)
  upper_error := v4309_upper_checked
  lower_error := reuse_lower_error 67 89 Primitive.Addresses.material4309

def v4310_pa : Scalar.QComplex := ((999997680173080625614633322989 : Int)/10^30,(-2153984321473077686362405546 : Int)/10^30)
theorem v4310_pa_checked : Scalar.distance (sourceCoefficient 67 90 1 0) v4310_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4310_pb : Scalar.QComplex := ((-929395783794772283703628 : Int)/10^30,(-431476505419415435304451463 : Int)/10^30)
theorem v4310_pb_checked : Scalar.distance (sourceCoefficient 67 90 1 1) v4310_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4310_pg : Scalar.QComplex := ((-93086212374649354452742 : Int)/10^30,(200506707141164638536 : Int)/10^30)
theorem v4310_pg_checked : Scalar.distance (sourceCoefficient 67 90 1 2) v4310_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4310_mb : Scalar.QComplex := ((-1301740228934784063620988 : Int)/10^30,(-431475542734290034553391312 : Int)/10^30)
theorem v4310_mb_checked : Scalar.distance (sourceCoefficient 67 90 3 1) v4310_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4310_mg : Scalar.QComplex := ((-93086004686140461338173 : Int)/10^30,(280835841315301961393 : Int)/10^30)
theorem v4310_mg_checked : Scalar.distance (sourceCoefficient 67 90 3 2) v4310_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4310_upper : Scalar.QComplex := ((999992473212473055668612020786 : Int)/10^30,(-3879886390264306052415682995 : Int)/10^30)
theorem v4310_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 67 90 5) 1) 14) v4310_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4310 : Material (67 : Basis) (90 : Basis) where
  plus := ![v4310_pa,v4310_pb,v4310_pg]
  minus := ![(Primitive.Addresses.material4310 1).one,v4310_mb,v4310_mg]
  upper := v4310_upper
  lower := (Primitive.Addresses.material4310 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4310_pa_checked.trans (by decide +kernel)
    · exact v4310_pb_checked.trans (by decide +kernel)
    · exact v4310_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 67 90 Primitive.Addresses.material4310
    · exact v4310_mb_checked.trans (by decide +kernel)
    · exact v4310_mg_checked.trans (by decide +kernel)
  upper_error := v4310_upper_checked
  lower_error := reuse_lower_error 67 90 Primitive.Addresses.material4310

def v4311_pa : Scalar.QComplex := ((999997648269020795118602515042 : Int)/10^30,(-2168745357982620384476533509 : Int)/10^30)
theorem v4311_pa_checked : Scalar.distance (sourceCoefficient 67 91 1 0) v4311_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4311_pb : Scalar.QComplex := ((-935764836908796791664848 : Int)/10^30,(-431476490680350070936943407 : Int)/10^30)
theorem v4311_pb_checked : Scalar.distance (sourceCoefficient 67 91 1 1) v4311_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4311_pg : Scalar.QComplex := ((-93086209299837919954521 : Int)/10^30,(201880759080457351434 : Int)/10^30)
theorem v4311_pg_checked : Scalar.distance (sourceCoefficient 67 91 1 2) v4311_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4311_mb : Scalar.QComplex := ((-1308109266958169430536512 : Int)/10^30,(-431475522499024172314203911 : Int)/10^30)
theorem v4311_mb_checked : Scalar.distance (sourceCoefficient 67 91 3 1) v4311_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4311_mg : Scalar.QComplex := ((-93086000425585233125230 : Int)/10^30,(282209890089548556411 : Int)/10^30)
theorem v4311_mg_checked : Scalar.distance (sourceCoefficient 67 91 3 2) v4311_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4311_upper : Scalar.QComplex := ((999992415832250837822874086047 : Int)/10^30,(-3894647349725505868980474145 : Int)/10^30)
theorem v4311_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 67 91 5) 1) 14) v4311_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4311 : Material (67 : Basis) (91 : Basis) where
  plus := ![v4311_pa,v4311_pb,v4311_pg]
  minus := ![(Primitive.Addresses.material4311 1).one,v4311_mb,v4311_mg]
  upper := v4311_upper
  lower := (Primitive.Addresses.material4311 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4311_pa_checked.trans (by decide +kernel)
    · exact v4311_pb_checked.trans (by decide +kernel)
    · exact v4311_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 67 91 Primitive.Addresses.material4311
    · exact v4311_mb_checked.trans (by decide +kernel)
    · exact v4311_mg_checked.trans (by decide +kernel)
  upper_error := v4311_upper_checked
  lower_error := reuse_lower_error 67 91 Primitive.Addresses.material4311

def v4312_pa : Scalar.QComplex := ((999997578453772101291618195825 : Int)/10^30,(-2200701386356468607462850255 : Int)/10^30)
theorem v4312_pa_checked : Scalar.distance (sourceCoefficient 67 92 1 0) v4312_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4312_pb : Scalar.QComplex := ((-949553139441235228952419 : Int)/10^30,(-431476458342451561210885980 : Int)/10^30)
theorem v4312_pb_checked : Scalar.distance (sourceCoefficient 67 92 1 1) v4312_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4312_pg : Scalar.QComplex := ((-93086202562142560497023 : Int)/10^30,(204855431096062628251 : Int)/10^30)
theorem v4312_pg_checked : Scalar.distance (sourceCoefficient 67 92 1 2) v4312_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4312_mb : Scalar.QComplex := ((-1321897536450442709430670 : Int)/10^30,(-431475478262453620064684969 : Int)/10^30)
theorem v4312_mb_checked : Scalar.distance (sourceCoefficient 67 92 3 1) v4312_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4312_mg : Scalar.QComplex := ((-93085991120884407206514 : Int)/10^30,(285184555183219851913 : Int)/10^30)
theorem v4312_mg_checked : Scalar.distance (sourceCoefficient 67 92 3 2) v4312_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4312_upper : Scalar.QComplex := ((999992290863900180593820752784 : Int)/10^30,(-3926603210009817992244882416 : Int)/10^30)
theorem v4312_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 67 92 5) 1) 14) v4312_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4312 : Material (67 : Basis) (92 : Basis) where
  plus := ![v4312_pa,v4312_pb,v4312_pg]
  minus := ![(Primitive.Addresses.material4312 1).one,v4312_mb,v4312_mg]
  upper := v4312_upper
  lower := (Primitive.Addresses.material4312 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4312_pa_checked.trans (by decide +kernel)
    · exact v4312_pb_checked.trans (by decide +kernel)
    · exact v4312_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 67 92 Primitive.Addresses.material4312
    · exact v4312_mb_checked.trans (by decide +kernel)
    · exact v4312_mg_checked.trans (by decide +kernel)
  upper_error := v4312_upper_checked
  lower_error := reuse_lower_error 67 92 Primitive.Addresses.material4312

def v4313_pa : Scalar.QComplex := ((999997494271651604899917905908 : Int)/10^30,(-2238626904626057649881657076 : Int)/10^30)
theorem v4313_pa_checked : Scalar.distance (sourceCoefficient 67 93 1 0) v4313_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4313_pb : Scalar.QComplex := ((-965917141061844425537964 : Int)/10^30,(-431476419201362708692375180 : Int)/10^30)
theorem v4313_pb_checked : Scalar.distance (sourceCoefficient 67 93 1 1) v4313_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4313_pg : Scalar.QComplex := ((-93086194421910838185784 : Int)/10^30,(208385781440301610997 : Int)/10^30)
theorem v4313_pg_checked : Scalar.distance (sourceCoefficient 67 93 1 2) v4313_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4313_mb : Scalar.QComplex := ((-1338261498200989400322136 : Int)/10^30,(-431475424999982950250649645 : Int)/10^30)
theorem v4313_mb_checked : Scalar.distance (sourceCoefficient 67 93 3 1) v4313_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4313_mg : Scalar.QComplex := ((-93085979934122369874437 : Int)/10^30,(288714897188294702590 : Int)/10^30)
theorem v4313_mg_checked : Scalar.distance (sourceCoefficient 67 93 3 2) v4313_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4313_upper : Scalar.QComplex := ((999992141225901106412297336784 : Int)/10^30,(-3964528526503099581979390064 : Int)/10^30)
theorem v4313_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 67 93 5) 1) 14) v4313_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4313 : Material (67 : Basis) (93 : Basis) where
  plus := ![v4313_pa,v4313_pb,v4313_pg]
  minus := ![(Primitive.Addresses.material4313 1).one,v4313_mb,v4313_mg]
  upper := v4313_upper
  lower := (Primitive.Addresses.material4313 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4313_pa_checked.trans (by decide +kernel)
    · exact v4313_pb_checked.trans (by decide +kernel)
    · exact v4313_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 67 93 Primitive.Addresses.material4313
    · exact v4313_mb_checked.trans (by decide +kernel)
    · exact v4313_mg_checked.trans (by decide +kernel)
  upper_error := v4313_upper_checked
  lower_error := reuse_lower_error 67 93 Primitive.Addresses.material4313

def v4314_pa : Scalar.QComplex := ((999997392980942675264109181966 : Int)/10^30,(-2283425347608523532762380040 : Int)/10^30)
theorem v4314_pa_checked : Scalar.distance (sourceCoefficient 67 94 1 0) v4314_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4314_pb : Scalar.QComplex := ((-985246653049809901536081 : Int)/10^30,(-431476371901045429332719640 : Int)/10^30)
theorem v4314_pb_checked : Scalar.distance (sourceCoefficient 67 94 1 1) v4314_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4314_pg : Scalar.QComplex := ((-93086184605259451730618 : Int)/10^30,(212555907577117556001 : Int)/10^30)
theorem v4314_pg_checked : Scalar.distance (sourceCoefficient 67 94 1 2) v4314_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4314_mb : Scalar.QComplex := ((-1357590962173650675983312 : Int)/10^30,(-431475361019185006249543929 : Int)/10^30)
theorem v4314_mb_checked : Scalar.distance (sourceCoefficient 67 94 3 1) v4314_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4314_mg : Scalar.QComplex := ((-93085966518843598044227 : Int)/10^30,(292885013301054081733 : Int)/10^30)
theorem v4314_mg_checked : Scalar.distance (sourceCoefficient 67 94 3 2) v4314_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4314_upper : Scalar.QComplex := ((999991962617294532653378084786 : Int)/10^30,(-4009326727944972446034967202 : Int)/10^30)
theorem v4314_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 67 94 5) 1) 14) v4314_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4314 : Material (67 : Basis) (94 : Basis) where
  plus := ![v4314_pa,v4314_pb,v4314_pg]
  minus := ![(Primitive.Addresses.material4314 1).one,v4314_mb,v4314_mg]
  upper := v4314_upper
  lower := (Primitive.Addresses.material4314 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4314_pa_checked.trans (by decide +kernel)
    · exact v4314_pb_checked.trans (by decide +kernel)
    · exact v4314_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 67 94 Primitive.Addresses.material4314
    · exact v4314_mb_checked.trans (by decide +kernel)
    · exact v4314_mg_checked.trans (by decide +kernel)
  upper_error := v4314_upper_checked
  lower_error := reuse_lower_error 67 94 Primitive.Addresses.material4314

def v4315_pa : Scalar.QComplex := ((999997290903957239761930043469 : Int)/10^30,(-2327699453606308522289237854 : Int)/10^30)
theorem v4315_pa_checked : Scalar.distance (sourceCoefficient 67 95 1 0) v4315_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4315_pb : Scalar.QComplex := ((-1004349924545715557531423 : Int)/10^30,(-431476324019955703349292475 : Int)/10^30)
theorem v4315_pb_checked : Scalar.distance (sourceCoefficient 67 95 1 1) v4315_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4315_pg : Scalar.QComplex := ((-93086174689364661313074 : Int)/10^30,(216677224962148209303 : Int)/10^30)
theorem v4315_pg_checked : Scalar.distance (sourceCoefficient 67 95 1 2) v4315_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4315_mb : Scalar.QComplex := ((-1376694185237311342120549 : Int)/10^30,(-431475296652850187026905146 : Int)/10^30)
theorem v4315_mb_checked : Scalar.distance (sourceCoefficient 67 95 3 1) v4315_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4315_mg : Scalar.QComplex := ((-93085953046441213730625 : Int)/10^30,(297006320594559310272 : Int)/10^30)
theorem v4315_mg_checked : Scalar.distance (sourceCoefficient 67 95 3 2) v4315_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4315_upper : Scalar.QComplex := ((999991784127370692174129817500 : Int)/10^30,(-4053600591826060843792034531 : Int)/10^30)
theorem v4315_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 67 95 5) 1) 14) v4315_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4315 : Material (67 : Basis) (95 : Basis) where
  plus := ![v4315_pa,v4315_pb,v4315_pg]
  minus := ![(Primitive.Addresses.material4315 1).one,v4315_mb,v4315_mg]
  upper := v4315_upper
  lower := (Primitive.Addresses.material4315 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4315_pa_checked.trans (by decide +kernel)
    · exact v4315_pb_checked.trans (by decide +kernel)
    · exact v4315_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 67 95 Primitive.Addresses.material4315
    · exact v4315_mb_checked.trans (by decide +kernel)
    · exact v4315_mg_checked.trans (by decide +kernel)
  upper_error := v4315_upper_checked
  lower_error := reuse_lower_error 67 95 Primitive.Addresses.material4315

def v4316_pa : Scalar.QComplex := ((999997241181450801704934582211 : Int)/10^30,(-2348963492120897721094796513 : Int)/10^30)
theorem v4316_pa_checked : Scalar.distance (sourceCoefficient 67 96 1 0) v4316_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4316_pb : Scalar.QComplex := ((-1013524874009264481548868 : Int)/10^30,(-431476300622673742889036999 : Int)/10^30)
theorem v4316_pb_checked : Scalar.distance (sourceCoefficient 67 96 1 1) v4316_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4316_pg : Scalar.QComplex := ((-93086169851268933437591 : Int)/10^30,(218656617835928891043 : Int)/10^30)
theorem v4316_pg_checked : Scalar.distance (sourceCoefficient 67 96 1 2) v4316_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4316_mb : Scalar.QComplex := ((-1385869111093806707537971 : Int)/10^30,(-431475265338008775785538789 : Int)/10^30)
theorem v4316_mb_checked : Scalar.distance (sourceCoefficient 67 96 3 1) v4316_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4316_mg : Scalar.QComplex := ((-93085946500220385772250 : Int)/10^30,(298985708556262848965 : Int)/10^30)
theorem v4316_mg_checked : Scalar.distance (sourceCoefficient 67 96 3 2) v4316_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4316_upper : Scalar.QComplex := ((999991697705136892273766254408 : Int)/10^30,(-4074864512853827203006581788 : Int)/10^30)
theorem v4316_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 67 96 5) 1) 14) v4316_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4316 : Material (67 : Basis) (96 : Basis) where
  plus := ![v4316_pa,v4316_pb,v4316_pg]
  minus := ![(Primitive.Addresses.material4316 1).one,v4316_mb,v4316_mg]
  upper := v4316_upper
  lower := (Primitive.Addresses.material4316 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4316_pa_checked.trans (by decide +kernel)
    · exact v4316_pb_checked.trans (by decide +kernel)
    · exact v4316_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 67 96 Primitive.Addresses.material4316
    · exact v4316_mb_checked.trans (by decide +kernel)
    · exact v4316_mg_checked.trans (by decide +kernel)
  upper_error := v4316_upper_checked
  lower_error := reuse_lower_error 67 96 Primitive.Addresses.material4316

def v4317_pa : Scalar.QComplex := ((999997066649711340280420987427 : Int)/10^30,(-2422125507230276285371685174 : Int)/10^30)
theorem v4317_pa_checked : Scalar.distance (sourceCoefficient 67 97 1 0) v4317_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4317_pb : Scalar.QComplex := ((-1045092619327622560001632 : Int)/10^30,(-431476218133698568263132965 : Int)/10^30)
theorem v4317_pb_checked : Scalar.distance (sourceCoefficient 67 97 1 1) v4317_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4317_pg : Scalar.QComplex := ((-93086152829965619794952 : Int)/10^30,(225467006513104133589 : Int)/10^30)
theorem v4317_pg_checked : Scalar.distance (sourceCoefficient 67 97 1 2) v4317_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4317_mb : Scalar.QComplex := ((-1417436773473780076559579 : Int)/10^30,(-431475155607521864302986514 : Int)/10^30)
theorem v4317_mb_checked : Scalar.distance (sourceCoefficient 67 97 3 1) v4317_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4317_mg : Scalar.QComplex := ((-93085923601864710056235 : Int)/10^30,(305796080009000988230 : Int)/10^30)
theorem v4317_mg_checked : Scalar.distance (sourceCoefficient 67 97 3 2) v4317_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4317_upper : Scalar.QComplex := ((999991396902656502749553762651 : Int)/10^30,(-4148026117771029561170983330 : Int)/10^30)
theorem v4317_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 67 97 5) 1) 14) v4317_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4317 : Material (67 : Basis) (97 : Basis) where
  plus := ![v4317_pa,v4317_pb,v4317_pg]
  minus := ![(Primitive.Addresses.material4317 1).one,v4317_mb,v4317_mg]
  upper := v4317_upper
  lower := (Primitive.Addresses.material4317 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4317_pa_checked.trans (by decide +kernel)
    · exact v4317_pb_checked.trans (by decide +kernel)
    · exact v4317_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 67 97 Primitive.Addresses.material4317
    · exact v4317_mb_checked.trans (by decide +kernel)
    · exact v4317_mg_checked.trans (by decide +kernel)
  upper_error := v4317_upper_checked
  lower_error := reuse_lower_error 67 97 Primitive.Addresses.material4317

def v4318_pa : Scalar.QComplex := ((999998338476684868979929253783 : Int)/10^30,(-1822921794702755046721312847 : Int)/10^30)
theorem v4318_pa_checked : Scalar.distance (sourceCoefficient 68 69 1 0) v4318_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4318_pb : Scalar.QComplex := ((-786549776895042771814454 : Int)/10^30,(-431476804057029913376806255 : Int)/10^30)
theorem v4318_pb_checked : Scalar.distance (sourceCoefficient 68 69 1 1) v4318_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4318_pg : Scalar.QComplex := ((-93086275228071391284319 : Int)/10^30,(169689281843648620518 : Int)/10^30)
theorem v4318_pg_checked : Scalar.distance (sourceCoefficient 68 69 1 2) v4318_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4318_mb : Scalar.QComplex := ((-1158894532933962461238166 : Int)/10^30,(-431475964641463725333696187 : Int)/10^30)
theorem v4318_mb_checked : Scalar.distance (sourceCoefficient 68 69 3 1) v4318_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4318_mg : Scalar.QComplex := ((-93086094133589161412800 : Int)/10^30,(250018481732194212296 : Int)/10^30)
theorem v4318_mg_checked : Scalar.distance (sourceCoefficient 68 69 3 2) v4318_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4318_upper : Scalar.QComplex := ((999993702898984280904274291213 : Int)/10^30,(-3548825492745027788533963908 : Int)/10^30)
theorem v4318_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 68 69 5) 1) 14) v4318_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4318 : Material (68 : Basis) (69 : Basis) where
  plus := ![v4318_pa,v4318_pb,v4318_pg]
  minus := ![(Primitive.Addresses.material4318 1).one,v4318_mb,v4318_mg]
  upper := v4318_upper
  lower := (Primitive.Addresses.material4318 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4318_pa_checked.trans (by decide +kernel)
    · exact v4318_pb_checked.trans (by decide +kernel)
    · exact v4318_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 68 69 Primitive.Addresses.material4318
    · exact v4318_mb_checked.trans (by decide +kernel)
    · exact v4318_mg_checked.trans (by decide +kernel)
  upper_error := v4318_upper_checked
  lower_error := reuse_lower_error 68 69 Primitive.Addresses.material4318

def v4319_pa : Scalar.QComplex := ((999998312431649304936708009566 : Int)/10^30,(-1837153737035414332699225945 : Int)/10^30)
theorem v4319_pa_checked : Scalar.distance (sourceCoefficient 68 70 1 0) v4319_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4319_pb : Scalar.QComplex := ((-792690539983163812867686 : Int)/10^30,(-431476792760330748090243554 : Int)/10^30)
theorem v4319_pb_checked : Scalar.distance (sourceCoefficient 68 70 1 1) v4319_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4319_pg : Scalar.QComplex := ((-93086272797283708196879 : Int)/10^30,(171014082534181004035 : Int)/10^30)
theorem v4319_pg_checked : Scalar.distance (sourceCoefficient 68 70 1 2) v4319_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4319_mb : Scalar.QComplex := ((-1165035283987054162647712 : Int)/10^30,(-431475948045566790978797963 : Int)/10^30)
theorem v4319_mb_checked : Scalar.distance (sourceCoefficient 68 70 3 1) v4319_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4319_mg : Scalar.QComplex := ((-93086090559559054297426 : Int)/10^30,(251343279831782460454 : Int)/10^30)
theorem v4319_mg_checked : Scalar.distance (sourceCoefficient 68 70 3 2) v4319_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4319_upper : Scalar.QComplex := ((999993652290946153434940852437 : Int)/10^30,(-3563057368929512175030596368 : Int)/10^30)
theorem v4319_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 68 70 5) 1) 14) v4319_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4319 : Material (68 : Basis) (70 : Basis) where
  plus := ![v4319_pa,v4319_pb,v4319_pg]
  minus := ![(Primitive.Addresses.material4319 1).one,v4319_mb,v4319_mg]
  upper := v4319_upper
  lower := (Primitive.Addresses.material4319 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4319_pa_checked.trans (by decide +kernel)
    · exact v4319_pb_checked.trans (by decide +kernel)
    · exact v4319_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 68 70 Primitive.Addresses.material4319
    · exact v4319_mb_checked.trans (by decide +kernel)
    · exact v4319_mg_checked.trans (by decide +kernel)
  upper_error := v4319_upper_checked
  lower_error := reuse_lower_error 68 70 Primitive.Addresses.material4319

def v4320_pa : Scalar.QComplex := ((999998267506940710708756248476 : Int)/10^30,(-1861446512002529177678412156 : Int)/10^30)
theorem v4320_pa_checked : Scalar.distance (sourceCoefficient 68 71 1 0) v4320_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4320_pb : Scalar.QComplex := ((-803172325989683228632296 : Int)/10^30,(-431476773208572192831572915 : Int)/10^30)
theorem v4320_pb_checked : Scalar.distance (sourceCoefficient 68 71 1 1) v4320_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4320_pg : Scalar.QComplex := ((-93086268597307163446606 : Int)/10^30,(173275410194233490717 : Int)/10^30)
theorem v4320_pg_checked : Scalar.distance (sourceCoefficient 68 71 1 2) v4320_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4320_mb : Scalar.QComplex := ((-1175517049218438552228010 : Int)/10^30,(-431475919448506274224362847 : Int)/10^30)
theorem v4320_mb_checked : Scalar.distance (sourceCoefficient 68 71 3 1) v4320_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4320_mg : Scalar.QComplex := ((-93086084408160149182165 : Int)/10^30,(253604603025448713321 : Int)/10^30)
theorem v4320_mg_checked : Scalar.distance (sourceCoefficient 68 71 3 2) v4320_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4320_upper : Scalar.QComplex := ((999993565439178699372684339758 : Int)/10^30,(-3587350030179420840386288861 : Int)/10^30)
theorem v4320_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 68 71 5) 1) 14) v4320_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4320 : Material (68 : Basis) (71 : Basis) where
  plus := ![v4320_pa,v4320_pb,v4320_pg]
  minus := ![(Primitive.Addresses.material4320 1).one,v4320_mb,v4320_mg]
  upper := v4320_upper
  lower := (Primitive.Addresses.material4320 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4320_pa_checked.trans (by decide +kernel)
    · exact v4320_pb_checked.trans (by decide +kernel)
    · exact v4320_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 68 71 Primitive.Addresses.material4320
    · exact v4320_mb_checked.trans (by decide +kernel)
    · exact v4320_mg_checked.trans (by decide +kernel)
  upper_error := v4320_upper_checked
  lower_error := reuse_lower_error 68 71 Primitive.Addresses.material4320

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
