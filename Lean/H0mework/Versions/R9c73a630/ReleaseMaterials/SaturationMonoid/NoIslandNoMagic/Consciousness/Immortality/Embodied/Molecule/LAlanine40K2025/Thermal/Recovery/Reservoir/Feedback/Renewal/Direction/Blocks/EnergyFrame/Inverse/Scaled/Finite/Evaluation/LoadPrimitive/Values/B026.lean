import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B017
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B018

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v417_pa : Scalar.QComplex := ((999993453033111109683105459820 : Int)/10^30,(3618548177792467856273252644 : Int)/10^30)
theorem v417_pa_checked : Scalar.distance (sourceCoefficient 4 40 1 0) v417_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v417_pb : Scalar.QComplex := ((1561316860868239284523146 : Int)/10^30,(-431473221376574048915096879 : Int)/10^30)
theorem v417_pb_checked : Scalar.distance (sourceCoefficient 4 40 1 1) v417_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v417_pg : Scalar.QComplex := ((-93085661382229731265639 : Int)/10^30,(-336837155634978978994 : Int)/10^30)
theorem v417_pg_checked : Scalar.distance (sourceCoefficient 4 40 1 2) v417_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v417_mb : Scalar.QComplex := ((1188974322303143022804096 : Int)/10^30,(-431474408065506258291195435 : Int)/10^30)
theorem v417_mb_checked : Scalar.distance (sourceCoefficient 4 40 3 1) v417_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v417_mg : Scalar.QComplex := ((-93085917397478504428916 : Int)/10^30,(-256508296864806074304 : Int)/10^30)
theorem v417_mg_checked : Scalar.distance (sourceCoefficient 4 40 3 2) v417_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v417_upper : Scalar.QComplex := ((999998208946213042929287725217 : Int)/10^30,(1892644807152275376798245549 : Int)/10^30)
theorem v417_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 40 5) 1) 14) v417_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material417 : Material (4 : Basis) (40 : Basis) where
  plus := ![v417_pa,v417_pb,v417_pg]
  minus := ![(Primitive.Addresses.material417 1).one,v417_mb,v417_mg]
  upper := v417_upper
  lower := (Primitive.Addresses.material417 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v417_pa_checked.trans (by decide +kernel)
    · exact v417_pb_checked.trans (by decide +kernel)
    · exact v417_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 40 Primitive.Addresses.material417
    · exact v417_mb_checked.trans (by decide +kernel)
    · exact v417_mg_checked.trans (by decide +kernel)
  upper_error := v417_upper_checked
  lower_error := reuse_lower_error 4 40 Primitive.Addresses.material417

def v418_pa : Scalar.QComplex := ((999993505339250138711605447098 : Int)/10^30,(3604064277881891634272760443 : Int)/10^30)
theorem v418_pa_checked : Scalar.distance (sourceCoefficient 4 41 1 0) v418_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v418_pb : Scalar.QComplex := ((1555067370946678749628958 : Int)/10^30,(-431473234496685597357007278 : Int)/10^30)
theorem v418_pb_checked : Scalar.distance (sourceCoefficient 4 41 1 1) v418_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v418_pg : Scalar.QComplex := ((-93085665231983281151805 : Int)/10^30,(-335488899732052434810 : Int)/10^30)
theorem v418_pg_checked : Scalar.distance (sourceCoefficient 4 41 1 2) v418_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v418_mb : Scalar.QComplex := ((1182724823386487843089258 : Int)/10^30,(-431474415792584585786752607 : Int)/10^30)
theorem v418_mb_checked : Scalar.distance (sourceCoefficient 4 41 3 1) v418_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v418_mg : Scalar.QComplex := ((-93085920083746499842002 : Int)/10^30,(-255160038141732894030 : Int)/10^30)
theorem v418_mg_checked : Scalar.distance (sourceCoefficient 4 41 3 2) v418_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v418_upper : Scalar.QComplex := ((999998236254376891589179373702 : Int)/10^30,(1878160838538115884963063558 : Int)/10^30)
theorem v418_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 41 5) 1) 14) v418_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material418 : Material (4 : Basis) (41 : Basis) where
  plus := ![v418_pa,v418_pb,v418_pg]
  minus := ![(Primitive.Addresses.material418 1).one,v418_mb,v418_mg]
  upper := v418_upper
  lower := (Primitive.Addresses.material418 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v418_pa_checked.trans (by decide +kernel)
    · exact v418_pb_checked.trans (by decide +kernel)
    · exact v418_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 41 Primitive.Addresses.material418
    · exact v418_mb_checked.trans (by decide +kernel)
    · exact v418_mg_checked.trans (by decide +kernel)
  upper_error := v418_upper_checked
  lower_error := reuse_lower_error 4 41 Primitive.Addresses.material418

def v419_pa : Scalar.QComplex := ((999993547379622144349785632981 : Int)/10^30,(3592380703572710110870993209 : Int)/10^30)
theorem v419_pa_checked : Scalar.distance (sourceCoefficient 4 42 1 0) v419_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v419_pb : Scalar.QComplex := ((1550026161148280965665572 : Int)/10^30,(-431473244992202108743073955 : Int)/10^30)
theorem v419_pb_checked : Scalar.distance (sourceCoefficient 4 42 1 1) v419_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v419_pg : Scalar.QComplex := ((-93085668320821705059360 : Int)/10^30,(-334401316419638120896 : Int)/10^30)
theorem v419_pg_checked : Scalar.distance (sourceCoefficient 4 42 1 2) v419_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v419_mb : Scalar.QComplex := ((1177683606408004812928911 : Int)/10^30,(-431474421937760180855980215 : Int)/10^30)
theorem v419_mb_checked : Scalar.distance (sourceCoefficient 4 42 3 1) v419_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v419_mg : Scalar.QComplex := ((-93085922234048357954352 : Int)/10^30,(-254072452568747108627 : Int)/10^30)
theorem v419_mg_checked : Scalar.distance (sourceCoefficient 4 42 3 2) v419_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v419_upper : Scalar.QComplex := ((999998258129896950966001449906 : Int)/10^30,(1866477209072377637064045159 : Int)/10^30)
theorem v419_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 42 5) 1) 14) v419_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material419 : Material (4 : Basis) (42 : Basis) where
  plus := ![v419_pa,v419_pb,v419_pg]
  minus := ![(Primitive.Addresses.material419 1).one,v419_mb,v419_mg]
  upper := v419_upper
  lower := (Primitive.Addresses.material419 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v419_pa_checked.trans (by decide +kernel)
    · exact v419_pb_checked.trans (by decide +kernel)
    · exact v419_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 42 Primitive.Addresses.material419
    · exact v419_mb_checked.trans (by decide +kernel)
    · exact v419_mg_checked.trans (by decide +kernel)
  upper_error := v419_upper_checked
  lower_error := reuse_lower_error 4 42 Primitive.Addresses.material419

def v420_pa : Scalar.QComplex := ((999993602861950676138852263720 : Int)/10^30,(3576903014518635252002423389 : Int)/10^30)
theorem v420_pa_checked : Scalar.distance (sourceCoefficient 4 43 1 0) v420_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v420_pb : Scalar.QComplex := ((1543347873006220193530256 : Int)/10^30,(-431473258775095544173314968 : Int)/10^30)
theorem v420_pb_checked : Scalar.distance (sourceCoefficient 4 43 1 1) v420_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v420_pg : Scalar.QComplex := ((-93085672389899139908873 : Int)/10^30,(-332960552174541567496 : Int)/10^30)
theorem v420_pg_checked : Scalar.distance (sourceCoefficient 4 43 1 2) v420_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v420_mb : Scalar.QComplex := ((1171005308858559652629129 : Int)/10^30,(-431474429957586596619119125 : Int)/10^30)
theorem v420_mb_checked : Scalar.distance (sourceCoefficient 4 43 3 1) v420_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v420_mg : Scalar.QComplex := ((-93085925059809623794827 : Int)/10^30,(-252631685348682368025 : Int)/10^30)
theorem v420_mg_checked : Scalar.distance (sourceCoefficient 4 43 3 2) v420_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v420_upper : Scalar.QComplex := ((999998286899055665993488943044 : Int)/10^30,(1850999447313036758824878564 : Int)/10^30)
theorem v420_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 43 5) 1) 14) v420_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material420 : Material (4 : Basis) (43 : Basis) where
  plus := ![v420_pa,v420_pb,v420_pg]
  minus := ![(Primitive.Addresses.material420 1).one,v420_mb,v420_mg]
  upper := v420_upper
  lower := (Primitive.Addresses.material420 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v420_pa_checked.trans (by decide +kernel)
    · exact v420_pb_checked.trans (by decide +kernel)
    · exact v420_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 43 Primitive.Addresses.material420
    · exact v420_mb_checked.trans (by decide +kernel)
    · exact v420_mg_checked.trans (by decide +kernel)
  upper_error := v420_upper_checked
  lower_error := reuse_lower_error 4 43 Primitive.Addresses.material420

def v421_pa : Scalar.QComplex := ((999993623790360788656423590795 : Int)/10^30,(3571047272492108018911156696 : Int)/10^30)
theorem v421_pa_checked : Scalar.distance (sourceCoefficient 4 44 1 0) v421_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v421_pb : Scalar.QComplex := ((1540821246994426597335564 : Int)/10^30,(-431473263953703202810151449 : Int)/10^30)
theorem v421_pb_checked : Scalar.distance (sourceCoefficient 4 44 1 1) v421_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v421_pg : Scalar.QComplex := ((-93085673922587569245927 : Int)/10^30,(-332415461520016051734 : Int)/10^30)
theorem v421_pg_checked : Scalar.distance (sourceCoefficient 4 44 1 2) v421_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v421_mb : Scalar.QComplex := ((1168478679318639219565624 : Int)/10^30,(-431474432955827873857078518 : Int)/10^30)
theorem v421_mb_checked : Scalar.distance (sourceCoefficient 4 44 3 1) v421_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v421_mg : Scalar.QComplex := ((-93085926122108797558153 : Int)/10^30,(-252086593574477930022 : Int)/10^30)
theorem v421_mg_checked : Scalar.distance (sourceCoefficient 4 44 3 2) v421_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v421_upper : Scalar.QComplex := ((999998297720955099083532260364 : Int)/10^30,(1845143677887412166796642582 : Int)/10^30)
theorem v421_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 44 5) 1) 14) v421_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material421 : Material (4 : Basis) (44 : Basis) where
  plus := ![v421_pa,v421_pb,v421_pg]
  minus := ![(Primitive.Addresses.material421 1).one,v421_mb,v421_mg]
  upper := v421_upper
  lower := (Primitive.Addresses.material421 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v421_pa_checked.trans (by decide +kernel)
    · exact v421_pb_checked.trans (by decide +kernel)
    · exact v421_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 44 Primitive.Addresses.material421
    · exact v421_mb_checked.trans (by decide +kernel)
    · exact v421_mg_checked.trans (by decide +kernel)
  upper_error := v421_upper_checked
  lower_error := reuse_lower_error 4 44 Primitive.Addresses.material421

def v422_pa : Scalar.QComplex := ((999993634189732819455939136997 : Int)/10^30,(3568133967611184071486783815 : Int)/10^30)
theorem v422_pa_checked : Scalar.distance (sourceCoefficient 4 45 1 0) v422_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v422_pb : Scalar.QComplex := ((1539564218969784645439589 : Int)/10^30,(-431473266522776541259293294 : Int)/10^30)
theorem v422_pb_checked : Scalar.distance (sourceCoefficient 4 45 1 1) v422_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v422_pg : Scalar.QComplex := ((-93085674683731996158806 : Int)/10^30,(-332144272104446147161 : Int)/10^30)
theorem v422_pg_checked : Scalar.distance (sourceCoefficient 4 45 1 2) v422_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v422_mb : Scalar.QComplex := ((1167221649545051665948930 : Int)/10^30,(-431474434440141684897402570 : Int)/10^30)
theorem v422_mb_checked : Scalar.distance (sourceCoefficient 4 45 3 1) v422_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v422_mg : Scalar.QComplex := ((-93085926649228689343224 : Int)/10^30,(-251815403603050879082 : Int)/10^30)
theorem v422_mg_checked : Scalar.distance (sourceCoefficient 4 45 3 2) v422_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v422_upper : Scalar.QComplex := ((999998303092211709719524888089 : Int)/10^30,(1842230359397140917178522937 : Int)/10^30)
theorem v422_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 45 5) 1) 14) v422_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material422 : Material (4 : Basis) (45 : Basis) where
  plus := ![v422_pa,v422_pb,v422_pg]
  minus := ![(Primitive.Addresses.material422 1).one,v422_mb,v422_mg]
  upper := v422_upper
  lower := (Primitive.Addresses.material422 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v422_pa_checked.trans (by decide +kernel)
    · exact v422_pb_checked.trans (by decide +kernel)
    · exact v422_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 45 Primitive.Addresses.material422
    · exact v422_mb_checked.trans (by decide +kernel)
    · exact v422_mg_checked.trans (by decide +kernel)
  upper_error := v422_upper_checked
  lower_error := reuse_lower_error 4 45 Primitive.Addresses.material422

def v423_pa : Scalar.QComplex := ((999993692445651588081499345204 : Int)/10^30,(3551769828069096432338274597 : Int)/10^30)
theorem v423_pa_checked : Scalar.distance (sourceCoefficient 4 46 1 0) v423_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v423_pb : Scalar.QComplex := ((1532503446934586561676631 : Int)/10^30,(-431473280862611300051415886 : Int)/10^30)
theorem v423_pb_checked : Scalar.distance (sourceCoefficient 4 46 1 1) v423_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v423_pg : Scalar.QComplex := ((-93085678941978099749098 : Int)/10^30,(-330620991301316024517 : Int)/10^30)
theorem v423_pg_checked : Scalar.distance (sourceCoefficient 4 46 1 2) v423_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v423_mb : Scalar.QComplex := ((1160160867764270149458742 : Int)/10^30,(-431474442686842843305286536 : Int)/10^30)
theorem v423_mb_checked : Scalar.distance (sourceCoefficient 4 46 3 1) v423_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v423_mg : Scalar.QComplex := ((-93085929592950480313182 : Int)/10^30,(-250292119692433213702 : Int)/10^30)
theorem v423_mg_checked : Scalar.distance (sourceCoefficient 4 46 3 2) v423_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v423_upper : Scalar.QComplex := ((999998333105023406496678550658 : Int)/10^30,(1825866143683086000126377308 : Int)/10^30)
theorem v423_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 46 5) 1) 14) v423_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material423 : Material (4 : Basis) (46 : Basis) where
  plus := ![v423_pa,v423_pb,v423_pg]
  minus := ![(Primitive.Addresses.material423 1).one,v423_mb,v423_mg]
  upper := v423_upper
  lower := (Primitive.Addresses.material423 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v423_pa_checked.trans (by decide +kernel)
    · exact v423_pb_checked.trans (by decide +kernel)
    · exact v423_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 46 Primitive.Addresses.material423
    · exact v423_mb_checked.trans (by decide +kernel)
    · exact v423_mg_checked.trans (by decide +kernel)
  upper_error := v423_upper_checked
  lower_error := reuse_lower_error 4 46 Primitive.Addresses.material423

def v424_pa : Scalar.QComplex := ((999993706424918802784094681370 : Int)/10^30,(3547831810177467973610478133 : Int)/10^30)
theorem v424_pa_checked : Scalar.distance (sourceCoefficient 4 47 1 0) v424_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v424_pb : Scalar.QComplex := ((1530804277479178543933317 : Int)/10^30,(-431473284290483578881010945 : Int)/10^30)
theorem v424_pb_checked : Scalar.distance (sourceCoefficient 4 47 1 1) v424_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v424_pg : Scalar.QComplex := ((-93085679962380418785832 : Int)/10^30,(-330254414923488797920 : Int)/10^30)
theorem v424_pg_checked : Scalar.distance (sourceCoefficient 4 47 1 2) v424_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v424_mb : Scalar.QComplex := ((1158461695983441184850656 : Int)/10^30,(-431474444648407133515679281 : Int)/10^30)
theorem v424_mb_checked : Scalar.distance (sourceCoefficient 4 47 3 1) v424_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v424_mg : Scalar.QComplex := ((-93085930297013515329779 : Int)/10^30,(-249925542570537881823 : Int)/10^30)
theorem v424_mg_checked : Scalar.distance (sourceCoefficient 4 47 3 2) v424_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v424_upper : Scalar.QComplex := ((999998340287608173964569835506 : Int)/10^30,(1821928107529725575540786158 : Int)/10^30)
theorem v424_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 47 5) 1) 14) v424_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material424 : Material (4 : Basis) (47 : Basis) where
  plus := ![v424_pa,v424_pb,v424_pg]
  minus := ![(Primitive.Addresses.material424 1).one,v424_mb,v424_mg]
  upper := v424_upper
  lower := (Primitive.Addresses.material424 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v424_pa_checked.trans (by decide +kernel)
    · exact v424_pb_checked.trans (by decide +kernel)
    · exact v424_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 47 Primitive.Addresses.material424
    · exact v424_mb_checked.trans (by decide +kernel)
    · exact v424_mg_checked.trans (by decide +kernel)
  upper_error := v424_upper_checked
  lower_error := reuse_lower_error 4 47 Primitive.Addresses.material424

def v425_pa : Scalar.QComplex := ((999993803367744227115442654659 : Int)/10^30,(3520401413659308231607651410 : Int)/10^30)
theorem v425_pa_checked : Scalar.distance (sourceCoefficient 4 48 1 0) v425_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v425_pb : Scalar.QComplex := ((1518968655647748254967101 : Int)/10^30,(-431473307919930452693616269 : Int)/10^30)
theorem v425_pb_checked : Scalar.distance (sourceCoefficient 4 48 1 1) v425_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v425_pg : Scalar.QComplex := ((-93085687023303714570486 : Int)/10^30,(-327701014830965071468 : Int)/10^30)
theorem v425_pg_checked : Scalar.distance (sourceCoefficient 4 48 1 2) v425_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v425_mb : Scalar.QComplex := ((1146626058167805397046174 : Int)/10^30,(-431474458064236625100250805 : Int)/10^30)
theorem v425_mb_checked : Scalar.distance (sourceCoefficient 4 48 3 1) v425_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v425_mg : Scalar.QComplex := ((-93085935154464903033148 : Int)/10^30,(-247372137335502913885 : Int)/10^30)
theorem v425_mg_checked : Scalar.distance (sourceCoefficient 4 48 3 2) v425_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v425_upper : Scalar.QComplex := ((999998389887913289134734577540 : Int)/10^30,(1794497584551397148641682026 : Int)/10^30)
theorem v425_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 48 5) 1) 14) v425_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material425 : Material (4 : Basis) (48 : Basis) where
  plus := ![v425_pa,v425_pb,v425_pg]
  minus := ![(Primitive.Addresses.material425 1).one,v425_mb,v425_mg]
  upper := v425_upper
  lower := (Primitive.Addresses.material425 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v425_pa_checked.trans (by decide +kernel)
    · exact v425_pb_checked.trans (by decide +kernel)
    · exact v425_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 48 Primitive.Addresses.material425
    · exact v425_mb_checked.trans (by decide +kernel)
    · exact v425_mg_checked.trans (by decide +kernel)
  upper_error := v425_upper_checked
  lower_error := reuse_lower_error 4 48 Primitive.Addresses.material425

def v426_pa : Scalar.QComplex := ((999993880708858958769400277181 : Int)/10^30,(3498363165304367363853579520 : Int)/10^30)
theorem v426_pa_checked : Scalar.distance (sourceCoefficient 4 49 1 0) v426_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v426_pb : Scalar.QComplex := ((1509459629379534007254923 : Int)/10^30,(-431473326590800011097659494 : Int)/10^30)
theorem v426_pb_checked : Scalar.distance (sourceCoefficient 4 49 1 1) v426_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v426_pg : Scalar.QComplex := ((-93085692637021941524802 : Int)/10^30,(-325649551082614546304 : Int)/10^30)
theorem v426_pg_checked : Scalar.distance (sourceCoefficient 4 49 1 2) v426_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v426_mb : Scalar.QComplex := ((1137117019328116688805870 : Int)/10^30,(-431474468529237832662327497 : Int)/10^30)
theorem v426_mb_checked : Scalar.distance (sourceCoefficient 4 49 3 1) v426_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v426_mg : Scalar.QComplex := ((-93085938997860219414486 : Int)/10^30,(-245320669506620101379 : Int)/10^30)
theorem v426_mg_checked : Scalar.distance (sourceCoefficient 4 49 3 2) v426_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v426_upper : Scalar.QComplex := ((999998429192895463928617633830 : Int)/10^30,(1772459235536090715352519764 : Int)/10^30)
theorem v426_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 49 5) 1) 14) v426_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material426 : Material (4 : Basis) (49 : Basis) where
  plus := ![v426_pa,v426_pb,v426_pg]
  minus := ![(Primitive.Addresses.material426 1).one,v426_mb,v426_mg]
  upper := v426_upper
  lower := (Primitive.Addresses.material426 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v426_pa_checked.trans (by decide +kernel)
    · exact v426_pb_checked.trans (by decide +kernel)
    · exact v426_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 49 Primitive.Addresses.material426
    · exact v426_mb_checked.trans (by decide +kernel)
    · exact v426_mg_checked.trans (by decide +kernel)
  upper_error := v426_upper_checked
  lower_error := reuse_lower_error 4 49 Primitive.Addresses.material426

def v427_pa : Scalar.QComplex := ((999993889714811484026863099202 : Int)/10^30,(3495787899951434593059530632 : Int)/10^30)
theorem v427_pa_checked : Scalar.distance (sourceCoefficient 4 50 1 0) v427_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v427_pb : Scalar.QComplex := ((1508348458250429303915729 : Int)/10^30,(-431473328754339018453833249 : Int)/10^30)
theorem v427_pb_checked : Scalar.distance (sourceCoefficient 4 50 1 1) v427_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v427_pg : Scalar.QComplex := ((-93085693289567416280117 : Int)/10^30,(-325409828607116161075 : Int)/10^30)
theorem v427_pg_checked : Scalar.distance (sourceCoefficient 4 50 1 2) v427_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v427_mb : Scalar.QComplex := ((1136005846745715058692980 : Int)/10^30,(-431474469733885395306577604 : Int)/10^30)
theorem v427_mb_checked : Scalar.distance (sourceCoefficient 4 50 3 1) v427_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v427_mg : Scalar.QComplex := ((-93085939443535751541696 : Int)/10^30,(-245080946557263994479 : Int)/10^30)
theorem v427_mg_checked : Scalar.distance (sourceCoefficient 4 50 3 2) v427_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v427_upper : Scalar.QComplex := ((999998433754160202963575157647 : Int)/10^30,(1769883958475256130869724512 : Int)/10^30)
theorem v427_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 50 5) 1) 14) v427_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material427 : Material (4 : Basis) (50 : Basis) where
  plus := ![v427_pa,v427_pb,v427_pg]
  minus := ![(Primitive.Addresses.material427 1).one,v427_mb,v427_mg]
  upper := v427_upper
  lower := (Primitive.Addresses.material427 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v427_pa_checked.trans (by decide +kernel)
    · exact v427_pb_checked.trans (by decide +kernel)
    · exact v427_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 50 Primitive.Addresses.material427
    · exact v427_mb_checked.trans (by decide +kernel)
    · exact v427_mg_checked.trans (by decide +kernel)
  upper_error := v427_upper_checked
  lower_error := reuse_lower_error 4 50 Primitive.Addresses.material427

def v428_pa : Scalar.QComplex := ((999993929150758557864692561839 : Int)/10^30,(3484488718258929633340199628 : Int)/10^30)
theorem v428_pa_checked : Scalar.distance (sourceCoefficient 4 51 1 0) v428_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v428_pb : Scalar.QComplex := ((1503473106552757775006428 : Int)/10^30,(-431473338201942801437280522 : Int)/10^30)
theorem v428_pb_checked : Scalar.distance (sourceCoefficient 4 51 1 1) v428_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v428_pg : Scalar.QComplex := ((-93085696144149807429454 : Int)/10^30,(-324358027174251977337 : Int)/10^30)
theorem v428_pg_checked : Scalar.distance (sourceCoefficient 4 51 1 2) v428_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v428_mb : Scalar.QComplex := ((1131130488710503220970846 : Int)/10^30,(-431474474974276723114186352 : Int)/10^30)
theorem v428_mb_checked : Scalar.distance (sourceCoefficient 4 51 3 1) v428_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v428_mg : Scalar.QComplex := ((-93085941390459814615785 : Int)/10^30,(-244029143052657515953 : Int)/10^30)
theorem v428_mg_checked : Scalar.distance (sourceCoefficient 4 51 3 2) v428_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v428_upper : Scalar.QComplex := ((999998453688685994083012955770 : Int)/10^30,(1758584725548687958745290803 : Int)/10^30)
theorem v428_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 51 5) 1) 14) v428_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material428 : Material (4 : Basis) (51 : Basis) where
  plus := ![v428_pa,v428_pb,v428_pg]
  minus := ![(Primitive.Addresses.material428 1).one,v428_mb,v428_mg]
  upper := v428_upper
  lower := (Primitive.Addresses.material428 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v428_pa_checked.trans (by decide +kernel)
    · exact v428_pb_checked.trans (by decide +kernel)
    · exact v428_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 51 Primitive.Addresses.material428
    · exact v428_mb_checked.trans (by decide +kernel)
    · exact v428_mg_checked.trans (by decide +kernel)
  upper_error := v428_upper_checked
  lower_error := reuse_lower_error 4 51 Primitive.Addresses.material428

def v429_pa : Scalar.QComplex := ((999994013144269158836766214393 : Int)/10^30,(3460299931977108911767585092 : Int)/10^30)
theorem v429_pa_checked : Scalar.distance (sourceCoefficient 4 52 1 0) v429_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v429_pb : Scalar.QComplex := ((1493036170552433922506147 : Int)/10^30,(-431473358180026341206411514 : Int)/10^30)
theorem v429_pb_checked : Scalar.distance (sourceCoefficient 4 52 1 1) v429_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v429_pg : Scalar.QComplex := ((-93085702208500154376781 : Int)/10^30,(-322106377424526125500 : Int)/10^30)
theorem v429_pg_checked : Scalar.distance (sourceCoefficient 4 52 1 2) v429_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v429_mb : Scalar.QComplex := ((1120693539356141317590696 : Int)/10^30,(-431474485945747117998214690 : Int)/10^30)
theorem v429_mb_checked : Scalar.distance (sourceCoefficient 4 52 3 1) v429_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v429_mg : Scalar.QComplex := ((-93085945511735580055106 : Int)/10^30,(-241777488908062550202 : Int)/10^30)
theorem v429_mg_checked : Scalar.distance (sourceCoefficient 4 52 3 2) v429_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v429_upper : Scalar.QComplex := ((999998495934420763714908187563 : Int)/10^30,(1734395830328043523990562598 : Int)/10^30)
theorem v429_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 52 5) 1) 14) v429_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material429 : Material (4 : Basis) (52 : Basis) where
  plus := ![v429_pa,v429_pb,v429_pg]
  minus := ![(Primitive.Addresses.material429 1).one,v429_mb,v429_mg]
  upper := v429_upper
  lower := (Primitive.Addresses.material429 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v429_pa_checked.trans (by decide +kernel)
    · exact v429_pb_checked.trans (by decide +kernel)
    · exact v429_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 52 Primitive.Addresses.material429
    · exact v429_mb_checked.trans (by decide +kernel)
    · exact v429_mg_checked.trans (by decide +kernel)
  upper_error := v429_upper_checked
  lower_error := reuse_lower_error 4 52 Primitive.Addresses.material429

def v430_pa : Scalar.QComplex := ((999994025949831775845951154328 : Int)/10^30,(3456597264243101786848627546 : Int)/10^30)
theorem v430_pa_checked : Scalar.distance (sourceCoefficient 4 53 1 0) v430_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v430_pb : Scalar.QComplex := ((1491438549875585962602166 : Int)/10^30,(-431473361208439074110810955 : Int)/10^30)
theorem v430_pb_checked : Scalar.distance (sourceCoefficient 4 53 1 1) v430_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v430_pg : Scalar.QComplex := ((-93085703131185032783086 : Int)/10^30,(-321761709003991521544 : Int)/10^30)
theorem v430_pg_checked : Scalar.distance (sourceCoefficient 4 53 1 2) v430_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v430_mb : Scalar.QComplex := ((1119095916660776756698936 : Int)/10^30,(-431474487595484033330580076 : Int)/10^30)
theorem v430_mb_checked : Scalar.distance (sourceCoefficient 4 53 3 1) v430_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v430_mg : Scalar.QComplex := ((-93085946136986791271707 : Int)/10^30,(-241432819819628257455 : Int)/10^30)
theorem v430_mg_checked : Scalar.distance (sourceCoefficient 4 53 3 2) v430_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v430_upper : Scalar.QComplex := ((999998502349495702839420353092 : Int)/10^30,(1730693146007485677577866839 : Int)/10^30)
theorem v430_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 53 5) 1) 14) v430_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material430 : Material (4 : Basis) (53 : Basis) where
  plus := ![v430_pa,v430_pb,v430_pg]
  minus := ![(Primitive.Addresses.material430 1).one,v430_mb,v430_mg]
  upper := v430_upper
  lower := (Primitive.Addresses.material430 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v430_pa_checked.trans (by decide +kernel)
    · exact v430_pb_checked.trans (by decide +kernel)
    · exact v430_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 53 Primitive.Addresses.material430
    · exact v430_mb_checked.trans (by decide +kernel)
    · exact v430_mg_checked.trans (by decide +kernel)
  upper_error := v430_upper_checked
  lower_error := reuse_lower_error 4 53 Primitive.Addresses.material430

def v431_pa : Scalar.QComplex := ((999994032455000597621796843005 : Int)/10^30,(3454714805481262372792637491 : Int)/10^30)
theorem v431_pa_checked : Scalar.distance (sourceCoefficient 4 54 1 0) v431_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v431_pb : Scalar.QComplex := ((1490626309825790001554263 : Int)/10^30,(-431473362745078150869106955 : Int)/10^30)
theorem v431_pb_checked : Scalar.distance (sourceCoefficient 4 54 1 1) v431_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v431_pg : Scalar.QComplex := ((-93085703599712716878521 : Int)/10^30,(-321586477486343562389 : Int)/10^30)
theorem v431_pg_checked : Scalar.distance (sourceCoefficient 4 54 1 2) v431_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v431_mb : Scalar.QComplex := ((1118283675587364571806669 : Int)/10^30,(-431474488431195956887863132 : Int)/10^30)
theorem v431_mb_checked : Scalar.distance (sourceCoefficient 4 54 3 1) v431_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v431_mg : Scalar.QComplex := ((-93085946454297393317269 : Int)/10^30,(-241257587962908711126 : Int)/10^30)
theorem v431_mg_checked : Scalar.distance (sourceCoefficient 4 54 3 2) v431_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v431_upper : Scalar.QComplex := ((999998505605701788320478597462 : Int)/10^30,(1728810678822016218062491040 : Int)/10^30)
theorem v431_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 54 5) 1) 14) v431_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material431 : Material (4 : Basis) (54 : Basis) where
  plus := ![v431_pa,v431_pb,v431_pg]
  minus := ![(Primitive.Addresses.material431 1).one,v431_mb,v431_mg]
  upper := v431_upper
  lower := (Primitive.Addresses.material431 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v431_pa_checked.trans (by decide +kernel)
    · exact v431_pb_checked.trans (by decide +kernel)
    · exact v431_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 54 Primitive.Addresses.material431
    · exact v431_mb_checked.trans (by decide +kernel)
    · exact v431_mg_checked.trans (by decide +kernel)
  upper_error := v431_upper_checked
  lower_error := reuse_lower_error 4 54 Primitive.Addresses.material431

def v432_pa : Scalar.QComplex := ((999994085345036703362618757807 : Int)/10^30,(3439371300608577781725272331 : Int)/10^30)
theorem v432_pa_checked : Scalar.distance (sourceCoefficient 4 55 1 0) v432_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v432_pb : Scalar.QComplex := ((1484005921001444448525691 : Int)/10^30,(-431473375193853925043141213 : Int)/10^30)
theorem v432_pb_checked : Scalar.distance (sourceCoefficient 4 55 1 1) v432_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v432_pg : Scalar.QComplex := ((-93085707404226012681874 : Int)/10^30,(-320158204168253663954 : Int)/10^30)
theorem v432_pg_checked : Scalar.distance (sourceCoefficient 4 55 1 2) v432_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v432_mb : Scalar.QComplex := ((1111663278485359523733870 : Int)/10^30,(-431474495166869711647538902 : Int)/10^30)
theorem v432_mb_checked : Scalar.distance (sourceCoefficient 4 55 3 1) v432_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v432_mg : Scalar.QComplex := ((-93085949026273726057179 : Int)/10^30,(-239829311893506618970 : Int)/10^30)
theorem v432_mg_checked : Scalar.distance (sourceCoefficient 4 55 3 2) v432_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v432_upper : Scalar.QComplex := ((999998532014161662200535404813 : Int)/10^30,(1713467105518275588252351991 : Int)/10^30)
theorem v432_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 55 5) 1) 14) v432_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material432 : Material (4 : Basis) (55 : Basis) where
  plus := ![v432_pa,v432_pb,v432_pg]
  minus := ![(Primitive.Addresses.material432 1).one,v432_mb,v432_mg]
  upper := v432_upper
  lower := (Primitive.Addresses.material432 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v432_pa_checked.trans (by decide +kernel)
    · exact v432_pb_checked.trans (by decide +kernel)
    · exact v432_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 55 Primitive.Addresses.material432
    · exact v432_mb_checked.trans (by decide +kernel)
    · exact v432_mg_checked.trans (by decide +kernel)
  upper_error := v432_upper_checked
  lower_error := reuse_lower_error 4 55 Primitive.Addresses.material432

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
