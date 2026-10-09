import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B015
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B016

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v369_pa : Scalar.QComplex := ((999995950152640405511670046919 : Int)/10^30,(2845993379810525955162515891 : Int)/10^30)
theorem v369_pa_checked : Scalar.distance (sourceCoefficient 3 85 1 0) v369_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v369_pb : Scalar.QComplex := ((1227976393697399215485201 : Int)/10^30,(-431473744560219824311083863 : Int)/10^30)
theorem v369_pb_checked : Scalar.distance (sourceCoefficient 3 85 1 1) v369_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v369_pg : Scalar.QComplex := ((-93085834041650994492574 : Int)/10^30,(-264922740333340460618 : Int)/10^30)
theorem v369_pg_checked : Scalar.distance (sourceCoefficient 3 85 1 2) v369_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v369_mb : Scalar.QComplex := ((855633527766270305942391 : Int)/10^30,(-431474643591147157399211923 : Int)/10^30)
theorem v369_mb_checked : Scalar.distance (sourceCoefficient 3 85 3 1) v369_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v369_mg : Scalar.QComplex := ((-93086027997933978379727 : Int)/10^30,(-184593759342886765371 : Int)/10^30)
theorem v369_mg_checked : Scalar.distance (sourceCoefficient 3 85 3 2) v369_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v369_upper : Scalar.QComplex := ((999999372702527479513583685799 : Int)/10^30,(1120086849998183757821095542 : Int)/10^30)
theorem v369_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 85 5) 1) 14) v369_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material369 : Material (3 : Basis) (85 : Basis) where
  plus := ![v369_pa,v369_pb,v369_pg]
  minus := ![(Primitive.Addresses.material369 1).one,v369_mb,v369_mg]
  upper := v369_upper
  lower := (Primitive.Addresses.material369 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v369_pa_checked.trans (by decide +kernel)
    · exact v369_pb_checked.trans (by decide +kernel)
    · exact v369_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 85 Primitive.Addresses.material369
    · exact v369_mb_checked.trans (by decide +kernel)
    · exact v369_mg_checked.trans (by decide +kernel)
  upper_error := v369_upper_checked
  lower_error := reuse_lower_error 3 85 Primitive.Addresses.material369

def v370_pa : Scalar.QComplex := ((999995991554085470202321736426 : Int)/10^30,(2831408794473335255466651539 : Int)/10^30)
theorem v370_pa_checked : Scalar.distance (sourceCoefficient 3 86 1 0) v370_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v370_pb : Scalar.QComplex := ((1221683470972295925308637 : Int)/10^30,(-431473751266432677309650964 : Int)/10^30)
theorem v370_pb_checked : Scalar.distance (sourceCoefficient 3 86 1 1) v370_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v370_pg : Scalar.QComplex := ((-93085836692001285403109 : Int)/10^30,(-263565113137142084402 : Int)/10^30)
theorem v370_pg_checked : Scalar.distance (sourceCoefficient 3 86 1 2) v370_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v370_mb : Scalar.QComplex := ((849340601597150091575095 : Int)/10^30,(-431474644866848624322498158 : Int)/10^30)
theorem v370_mb_checked : Scalar.distance (sourceCoefficient 3 86 3 1) v370_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v370_mg : Scalar.QComplex := ((-93086029476712157383621 : Int)/10^30,(-183236130365062107217 : Int)/10^30)
theorem v370_mg_checked : Scalar.distance (sourceCoefficient 3 86 3 2) v370_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v370_upper : Scalar.QComplex := ((999999388932239692870293789734 : Int)/10^30,(1105502214927881420230174586 : Int)/10^30)
theorem v370_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 86 5) 1) 14) v370_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material370 : Material (3 : Basis) (86 : Basis) where
  plus := ![v370_pa,v370_pb,v370_pg]
  minus := ![(Primitive.Addresses.material370 1).one,v370_mb,v370_mg]
  upper := v370_upper
  lower := (Primitive.Addresses.material370 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v370_pa_checked.trans (by decide +kernel)
    · exact v370_pb_checked.trans (by decide +kernel)
    · exact v370_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 86 Primitive.Addresses.material370
    · exact v370_mb_checked.trans (by decide +kernel)
    · exact v370_mg_checked.trans (by decide +kernel)
  upper_error := v370_upper_checked
  lower_error := reuse_lower_error 3 86 Primitive.Addresses.material370

def v371_pa : Scalar.QComplex := ((999995994288070408032429628223 : Int)/10^30,(2830443041902781739377242004 : Int)/10^30)
theorem v371_pa_checked : Scalar.distance (sourceCoefficient 3 87 1 0) v371_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v371_pb : Scalar.QComplex := ((1221266770323317874313695 : Int)/10^30,(-431473751706180386579574376 : Int)/10^30)
theorem v371_pb_checked : Scalar.distance (sourceCoefficient 3 87 1 1) v371_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v371_pg : Scalar.QComplex := ((-93085836866684974355670 : Int)/10^30,(-263475214664816458782 : Int)/10^30)
theorem v371_pg_checked : Scalar.distance (sourceCoefficient 3 87 1 2) v371_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v371_mb : Scalar.QComplex := ((848923900723846268756807 : Int)/10^30,(-431474644947002277286741540 : Int)/10^30)
theorem v371_mb_checked : Scalar.distance (sourceCoefficient 3 87 3 1) v371_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v371_mg : Scalar.QComplex := ((-93086029573817448553339 : Int)/10^30,(-183146231775465635303 : Int)/10^30)
theorem v371_mg_checked : Scalar.distance (sourceCoefficient 3 87 3 2) v371_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v371_upper : Scalar.QComplex := ((999999389999419234364434635911 : Int)/10^30,(1104536459077092935195522133 : Int)/10^30)
theorem v371_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 87 5) 1) 14) v371_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material371 : Material (3 : Basis) (87 : Basis) where
  plus := ![v371_pa,v371_pb,v371_pg]
  minus := ![(Primitive.Addresses.material371 1).one,v371_mb,v371_mg]
  upper := v371_upper
  lower := (Primitive.Addresses.material371 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v371_pa_checked.trans (by decide +kernel)
    · exact v371_pb_checked.trans (by decide +kernel)
    · exact v371_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 87 Primitive.Addresses.material371
    · exact v371_mb_checked.trans (by decide +kernel)
    · exact v371_mg_checked.trans (by decide +kernel)
  upper_error := v371_upper_checked
  lower_error := reuse_lower_error 3 87 Primitive.Addresses.material371

def v372_pa : Scalar.QComplex := ((999996027503786418550790578436 : Int)/10^30,(2818683495257445803581773925 : Int)/10^30)
theorem v372_pa_checked : Scalar.distance (sourceCoefficient 3 88 1 0) v372_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v372_pb : Scalar.QComplex := ((1216192788863902989337594 : Int)/10^30,(-431473757017750279309092353 : Int)/10^30)
theorem v372_pb_checked : Scalar.distance (sourceCoefficient 3 88 1 1) v372_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v372_pg : Scalar.QComplex := ((-93085838985606049991161 : Int)/10^30,(-262380560296702170330 : Int)/10^30)
theorem v372_pg_checked : Scalar.distance (sourceCoefficient 3 88 1 2) v372_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v372_mb : Scalar.QComplex := ((843849916570060980331254 : Int)/10^30,(-431474645879952716442727692 : Int)/10^30)
theorem v372_mb_checked : Scalar.distance (sourceCoefficient 3 88 3 1) v372_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v372_mg : Scalar.QComplex := ((-93086030748100316937629 : Int)/10^30,(-182051575986407740665 : Int)/10^30)
theorem v372_mg_checked : Scalar.distance (sourceCoefficient 3 88 3 2) v372_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v372_upper : Scalar.QComplex := ((999999402919175081863906860643 : Int)/10^30,(1092776872618907826305908270 : Int)/10^30)
theorem v372_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 88 5) 1) 14) v372_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material372 : Material (3 : Basis) (88 : Basis) where
  plus := ![v372_pa,v372_pb,v372_pg]
  minus := ![(Primitive.Addresses.material372 1).one,v372_mb,v372_mg]
  upper := v372_upper
  lower := (Primitive.Addresses.material372 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v372_pa_checked.trans (by decide +kernel)
    · exact v372_pb_checked.trans (by decide +kernel)
    · exact v372_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 88 Primitive.Addresses.material372
    · exact v372_mb_checked.trans (by decide +kernel)
    · exact v372_mg_checked.trans (by decide +kernel)
  upper_error := v372_upper_checked
  lower_error := reuse_lower_error 3 88 Primitive.Addresses.material372

def v373_pa : Scalar.QComplex := ((999996072725515659161227157507 : Int)/10^30,(2802594074281325920445222837 : Int)/10^30)
theorem v373_pa_checked : Scalar.distance (sourceCoefficient 3 89 1 0) v373_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v373_pb : Scalar.QComplex := ((1209250563690780047544922 : Int)/10^30,(-431473764156154187357673620 : Int)/10^30)
theorem v373_pb_checked : Scalar.distance (sourceCoefficient 3 89 1 1) v373_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v373_pg : Scalar.QComplex := ((-93085841860384696075017 : Int)/10^30,(-260882853355976131680 : Int)/10^30)
theorem v373_pg_checked : Scalar.distance (sourceCoefficient 3 89 1 2) v373_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v373_mb : Scalar.QComplex := ((836907687821724674987772 : Int)/10^30,(-431474647027526308347276025 : Int)/10^30)
theorem v373_mb_checked : Scalar.distance (sourceCoefficient 3 89 3 1) v373_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v373_mg : Scalar.QComplex := ((-93086032330424256980032 : Int)/10^30,(-180553867122541948289 : Int)/10^30)
theorem v373_mg_checked : Scalar.distance (sourceCoefficient 3 89 3 2) v373_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v373_upper : Scalar.QComplex := ((999999420371955986106859816003 : Int)/10^30,(1076687397557488304883333866 : Int)/10^30)
theorem v373_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 89 5) 1) 14) v373_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material373 : Material (3 : Basis) (89 : Basis) where
  plus := ![v373_pa,v373_pb,v373_pg]
  minus := ![(Primitive.Addresses.material373 1).one,v373_mb,v373_mg]
  upper := v373_upper
  lower := (Primitive.Addresses.material373 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v373_pa_checked.trans (by decide +kernel)
    · exact v373_pb_checked.trans (by decide +kernel)
    · exact v373_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 89 Primitive.Addresses.material373
    · exact v373_mb_checked.trans (by decide +kernel)
    · exact v373_mg_checked.trans (by decide +kernel)
  upper_error := v373_upper_checked
  lower_error := reuse_lower_error 3 89 Primitive.Addresses.material373

def v374_pa : Scalar.QComplex := ((999996145818429007862355704937 : Int)/10^30,(2776391234546870037565626182 : Int)/10^30)
theorem v374_pa_checked : Scalar.distance (sourceCoefficient 3 90 1 0) v374_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v374_pb : Scalar.QComplex := ((1197944625227897782438056 : Int)/10^30,(-431473775462813638964069584 : Int)/10^30)
theorem v374_pb_checked : Scalar.distance (sourceCoefficient 3 90 1 1) v374_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v374_pg : Scalar.QComplex := ((-93085846482004201697665 : Int)/10^30,(-258443724322051485330 : Int)/10^30)
theorem v374_pg_checked : Scalar.distance (sourceCoefficient 3 90 1 2) v374_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v374_mb : Scalar.QComplex := ((825601743811422132827329 : Int)/10^30,(-431474648577665857066178198 : Int)/10^30)
theorem v374_mb_checked : Scalar.distance (sourceCoefficient 3 90 3 1) v374_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v374_mg : Scalar.QComplex := ((-93086034847183539779254 : Int)/10^30,(-178114735008567031637 : Int)/10^30)
theorem v374_mg_checked : Scalar.distance (sourceCoefficient 3 90 3 2) v374_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v374_upper : Scalar.QComplex := ((999999448241036192880598194199 : Int)/10^30,(1050484470697346702145540548 : Int)/10^30)
theorem v374_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 90 5) 1) 14) v374_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material374 : Material (3 : Basis) (90 : Basis) where
  plus := ![v374_pa,v374_pb,v374_pg]
  minus := ![(Primitive.Addresses.material374 1).one,v374_mb,v374_mg]
  upper := v374_upper
  lower := (Primitive.Addresses.material374 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v374_pa_checked.trans (by decide +kernel)
    · exact v374_pb_checked.trans (by decide +kernel)
    · exact v374_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 90 Primitive.Addresses.material374
    · exact v374_mb_checked.trans (by decide +kernel)
    · exact v374_mg_checked.trans (by decide +kernel)
  upper_error := v374_upper_checked
  lower_error := reuse_lower_error 3 90 Primitive.Addresses.material374

def v375_pa : Scalar.QComplex := ((999996186691992921170094153939 : Int)/10^30,(2761630220148907437751111528 : Int)/10^30)
theorem v375_pa_checked : Scalar.distance (sourceCoefficient 3 91 1 0) v375_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v375_pb : Scalar.QComplex := ((1191575578474274891288778 : Int)/10^30,(-431473781658331795219193330 : Int)/10^30)
theorem v375_pb_checked : Scalar.distance (sourceCoefficient 3 91 1 1) v375_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v375_pg : Scalar.QComplex := ((-93085849052696824518012 : Int)/10^30,(-257069674097993713385 : Int)/10^30)
theorem v375_pg_checked : Scalar.distance (sourceCoefficient 3 91 1 2) v375_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v375_mb : Scalar.QComplex := ((819232694082833294799418 : Int)/10^30,(-431474649276981209287553594 : Int)/10^30)
theorem v375_mb_checked : Scalar.distance (sourceCoefficient 3 91 3 1) v375_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v375_mg : Scalar.QComplex := ((-93086036232131746976209 : Int)/10^30,(-176740683077739001510 : Int)/10^30)
theorem v375_mg_checked : Scalar.distance (sourceCoefficient 3 91 3 2) v375_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v375_upper : Scalar.QComplex := ((999999463638367487698426132581 : Int)/10^30,(1035723407740117803925340683 : Int)/10^30)
theorem v375_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 91 5) 1) 14) v375_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material375 : Material (3 : Basis) (91 : Basis) where
  plus := ![v375_pa,v375_pb,v375_pg]
  minus := ![(Primitive.Addresses.material375 1).one,v375_mb,v375_mg]
  upper := v375_upper
  lower := (Primitive.Addresses.material375 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v375_pa_checked.trans (by decide +kernel)
    · exact v375_pb_checked.trans (by decide +kernel)
    · exact v375_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 91 Primitive.Addresses.material375
    · exact v375_mb_checked.trans (by decide +kernel)
    · exact v375_mg_checked.trans (by decide +kernel)
  upper_error := v375_upper_checked
  lower_error := reuse_lower_error 3 91 Primitive.Addresses.material375

def v376_pa : Scalar.QComplex := ((999996274432342830166881511946 : Int)/10^30,(2729674235963936061243538873 : Int)/10^30)
theorem v376_pa_checked : Scalar.distance (sourceCoefficient 3 92 1 0) v376_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v376_pb : Scalar.QComplex := ((1177787288652773344664606 : Int)/10^30,(-431473794641517200679917128 : Int)/10^30)
theorem v376_pb_checked : Scalar.distance (sourceCoefficient 3 92 1 1) v376_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v376_pg : Scalar.QComplex := ((-93085854536900423657898 : Int)/10^30,(-254095005510198132384 : Int)/10^30)
theorem v376_pg_checked : Scalar.distance (sourceCoefficient 3 92 1 2) v376_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v376_mb : Scalar.QComplex := ((805444398191437940746904 : Int)/10^30,(-431474650361488666080055690 : Int)/10^30)
theorem v376_mb_checked : Scalar.distance (sourceCoefficient 3 92 3 1) v376_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v376_mg : Scalar.QComplex := ((-93086039149328286928710 : Int)/10^30,(-173766010864927778119 : Int)/10^30)
theorem v376_mg_checked : Scalar.distance (sourceCoefficient 3 92 3 2) v376_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v376_upper : Scalar.QComplex := ((999999496225457038729459712806 : Int)/10^30,(1003767319717946856776437845 : Int)/10^30)
theorem v376_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 92 5) 1) 14) v376_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material376 : Material (3 : Basis) (92 : Basis) where
  plus := ![v376_pa,v376_pb,v376_pg]
  minus := ![(Primitive.Addresses.material376 1).one,v376_mb,v376_mg]
  upper := v376_upper
  lower := (Primitive.Addresses.material376 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v376_pa_checked.trans (by decide +kernel)
    · exact v376_pb_checked.trans (by decide +kernel)
    · exact v376_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 92 Primitive.Addresses.material376
    · exact v376_mb_checked.trans (by decide +kernel)
    · exact v376_mg_checked.trans (by decide +kernel)
  upper_error := v376_upper_checked
  lower_error := reuse_lower_error 3 92 Primitive.Addresses.material376

def v377_pa : Scalar.QComplex := ((999996377237734614012123529925 : Int)/10^30,(2691748763604349507591852998 : Int)/10^30)
theorem v377_pa_checked : Scalar.distance (sourceCoefficient 3 93 1 0) v377_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v377_pb : Scalar.QComplex := ((1161423300238174047563108 : Int)/10^30,(-431473809287641463462827534 : Int)/10^30)
theorem v377_pb_checked : Scalar.distance (sourceCoefficient 3 93 1 1) v377_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v377_pg : Scalar.QComplex := ((-93085860901659152108712 : Int)/10^30,(-250564658727278158037 : Int)/10^30)
theorem v377_pg_checked : Scalar.distance (sourceCoefficient 3 93 1 2) v377_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v377_mb : Scalar.QComplex := ((789080403230953799785129 : Int)/10^30,(-431474650886222480321568317 : Int)/10^30)
theorem v377_mb_checked : Scalar.distance (sourceCoefficient 3 93 3 1) v377_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v377_mg : Scalar.QComplex := ((-93086042467554372745739 : Int)/10^30,(-170235659904017131310 : Int)/10^30)
theorem v377_mg_checked : Scalar.distance (sourceCoefficient 3 93 3 2) v377_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v377_upper : Scalar.QComplex := ((999999533574770985349806068923 : Int)/10^30,(965841726411116557167802091 : Int)/10^30)
theorem v377_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 93 5) 1) 14) v377_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material377 : Material (3 : Basis) (93 : Basis) where
  plus := ![v377_pa,v377_pb,v377_pg]
  minus := ![(Primitive.Addresses.material377 1).one,v377_mb,v377_mg]
  upper := v377_upper
  lower := (Primitive.Addresses.material377 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v377_pa_checked.trans (by decide +kernel)
    · exact v377_pb_checked.trans (by decide +kernel)
    · exact v377_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 93 Primitive.Addresses.material377
    · exact v377_mb_checked.trans (by decide +kernel)
    · exact v377_mg_checked.trans (by decide +kernel)
  upper_error := v377_upper_checked
  lower_error := reuse_lower_error 3 93 Primitive.Addresses.material377

def v378_pa : Scalar.QComplex := ((999996496820744585572636166874 : Int)/10^30,(2646950365715979790609317432 : Int)/10^30)
theorem v378_pa_checked : Scalar.distance (sourceCoefficient 3 94 1 0) v378_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v378_pb : Scalar.QComplex := ((1142093801221508743541960 : Int)/10^30,(-431473825521949304740113788 : Int)/10^30)
theorem v378_pb_checked : Scalar.distance (sourceCoefficient 3 94 1 1) v378_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v378_pg : Scalar.QComplex := ((-93085868218617901764741 : Int)/10^30,(-246394536088487627959 : Int)/10^30)
theorem v378_pg_checked : Scalar.distance (sourceCoefficient 3 94 1 2) v378_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v378_mb : Scalar.QComplex := ((769750897402067880475179 : Int)/10^30,(-431474650440037193760638913 : Int)/10^30)
theorem v378_mb_checked : Scalar.distance (sourceCoefficient 3 94 3 1) v378_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v378_mg : Scalar.QComplex := ((-93086046185882376039014 : Int)/10^30,(-166065532503747986309 : Int)/10^30)
theorem v378_mg_checked : Scalar.distance (sourceCoefficient 3 94 3 2) v378_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v378_upper : Scalar.QComplex := ((999999575839632175647632343001 : Int)/10^30,(921043188855271380440746883 : Int)/10^30)
theorem v378_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 94 5) 1) 14) v378_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material378 : Material (3 : Basis) (94 : Basis) where
  plus := ![v378_pa,v378_pb,v378_pg]
  minus := ![(Primitive.Addresses.material378 1).one,v378_mb,v378_mg]
  upper := v378_upper
  lower := (Primitive.Addresses.material378 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v378_pa_checked.trans (by decide +kernel)
    · exact v378_pb_checked.trans (by decide +kernel)
    · exact v378_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 94 Primitive.Addresses.material378
    · exact v378_mb_checked.trans (by decide +kernel)
    · exact v378_mg_checked.trans (by decide +kernel)
  upper_error := v378_upper_checked
  lower_error := reuse_lower_error 3 94 Primitive.Addresses.material378

def v379_pa : Scalar.QComplex := ((999996613032317085608764535562 : Int)/10^30,(2602676294562713644967017387 : Int)/10^30)
theorem v379_pa_checked : Scalar.distance (sourceCoefficient 3 95 1 0) v379_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v379_pb : Scalar.QComplex := ((1122990539748597932893087 : Int)/10^30,(-431473840431857934441019816 : Int)/10^30)
theorem v379_pb_checked : Scalar.distance (sourceCoefficient 3 95 1 1) v379_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v379_pg : Scalar.QComplex := ((-93085875235796935492579 : Int)/10^30,(-242273221406402375401 : Int)/10^30)
theorem v379_pg_checked : Scalar.distance (sourceCoefficient 3 95 1 2) v379_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v379_mb : Scalar.QComplex := ((750647630175594748295363 : Int)/10^30,(-431474648864685999657087715 : Int)/10^30)
theorem v379_mb_checked : Scalar.distance (sourceCoefficient 3 95 3 1) v379_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v379_mg : Scalar.QComplex := ((-93086049646549843433674 : Int)/10^30,(-161944213300707079182 : Int)/10^30)
theorem v379_mg_checked : Scalar.distance (sourceCoefficient 3 95 3 2) v379_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v379_upper : Scalar.QComplex := ((999999615638001294020076352374 : Int)/10^30,(876768983072401916294921204 : Int)/10^30)
theorem v379_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 95 5) 1) 14) v379_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material379 : Material (3 : Basis) (95 : Basis) where
  plus := ![v379_pa,v379_pb,v379_pg]
  minus := ![(Primitive.Addresses.material379 1).one,v379_mb,v379_mg]
  upper := v379_upper
  lower := (Primitive.Addresses.material379 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v379_pa_checked.trans (by decide +kernel)
    · exact v379_pb_checked.trans (by decide +kernel)
    · exact v379_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 95 Primitive.Addresses.material379
    · exact v379_mb_checked.trans (by decide +kernel)
    · exact v379_mg_checked.trans (by decide +kernel)
  upper_error := v379_upper_checked
  lower_error := reuse_lower_error 3 95 Primitive.Addresses.material379

def v380_pa : Scalar.QComplex := ((999996668149797217462872720067 : Int)/10^30,(2581412269347788714915481303 : Int)/10^30)
theorem v380_pa_checked : Scalar.distance (sourceCoefficient 3 96 1 0) v380_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v380_pb : Scalar.QComplex := ((1113815594110677429459428 : Int)/10^30,(-431473847191939024061501392 : Int)/10^30)
theorem v380_pb_checked : Scalar.distance (sourceCoefficient 3 96 1 1) v380_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v380_pg : Scalar.QComplex := ((-93085878530345573329302 : Int)/10^30,(-240293829564296731067 : Int)/10^30)
theorem v380_pg_checked : Scalar.distance (sourceCoefficient 3 96 1 2) v380_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v380_mb : Scalar.QComplex := ((741472682120280303997391 : Int)/10^30,(-431474647707199710876962342 : Int)/10^30)
theorem v380_mb_checked : Scalar.distance (sourceCoefficient 3 96 3 1) v380_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v380_mg : Scalar.QComplex := ((-93086051232971243321420 : Int)/10^30,(-159964819352572386850 : Int)/10^30)
theorem v380_mg_checked : Scalar.distance (sourceCoefficient 3 96 3 2) v380_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v380_upper : Scalar.QComplex := ((999999634055620871200182234435 : Int)/10^30,(855504894399974207165886668 : Int)/10^30)
theorem v380_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 96 5) 1) 14) v380_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material380 : Material (3 : Basis) (96 : Basis) where
  plus := ![v380_pa,v380_pb,v380_pg]
  minus := ![(Primitive.Addresses.material380 1).one,v380_mb,v380_mg]
  upper := v380_upper
  lower := (Primitive.Addresses.material380 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v380_pa_checked.trans (by decide +kernel)
    · exact v380_pb_checked.trans (by decide +kernel)
    · exact v380_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 96 Primitive.Addresses.material380
    · exact v380_mb_checked.trans (by decide +kernel)
    · exact v380_mg_checked.trans (by decide +kernel)
  upper_error := v380_upper_checked
  lower_error := reuse_lower_error 3 96 Primitive.Addresses.material380

def v381_pa : Scalar.QComplex := ((999996854335311394209067576054 : Int)/10^30,(2508250282967241832556625002 : Int)/10^30)
theorem v381_pa_checked : Scalar.distance (sourceCoefficient 3 97 1 0) v381_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v381_pb : Scalar.QComplex := ((1082247857056073857001872 : Int)/10^30,(-431473868463763625798160532 : Int)/10^30)
theorem v381_pb_checked : Scalar.distance (sourceCoefficient 3 97 1 1) v381_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v381_pg : Scalar.QComplex := ((-93085889490589991596123 : Int)/10^30,(-233483443115652132109 : Int)/10^30)
theorem v381_pg_checked : Scalar.distance (sourceCoefficient 3 97 1 2) v381_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v381_mb : Scalar.QComplex := ((709904938463161369940732 : Int)/10^30,(-431474641737481072117066674 : Int)/10^30)
theorem v381_mb_checked : Scalar.distance (sourceCoefficient 3 97 3 1) v381_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v381_mg : Scalar.QComplex := ((-93086056316154803827400 : Int)/10^30,(-153154425981548610879 : Int)/10^30)
theorem v381_mg_checked : Scalar.distance (sourceCoefficient 3 97 3 2) v381_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v381_upper : Scalar.QComplex := ((999999693969906457227433018460 : Int)/10^30,(782342695646304976840898871 : Int)/10^30)
theorem v381_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 97 5) 1) 14) v381_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material381 : Material (3 : Basis) (97 : Basis) where
  plus := ![v381_pa,v381_pb,v381_pg]
  minus := ![(Primitive.Addresses.material381 1).one,v381_mb,v381_mg]
  upper := v381_upper
  lower := (Primitive.Addresses.material381 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v381_pa_checked.trans (by decide +kernel)
    · exact v381_pb_checked.trans (by decide +kernel)
    · exact v381_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 97 Primitive.Addresses.material381
    · exact v381_mb_checked.trans (by decide +kernel)
    · exact v381_mg_checked.trans (by decide +kernel)
  upper_error := v381_upper_checked
  lower_error := reuse_lower_error 3 97 Primitive.Addresses.material381

def v382_pa : Scalar.QComplex := ((999967014807412128039997299700 : Int)/10^30,(8122148555204704023482915250 : Int)/10^30)
theorem v382_pa_checked : Scalar.distance (sourceCoefficient 4 5 1 0) v382_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v382_pb : Scalar.QComplex := ((3504524523437858545734866 : Int)/10^30,(-431463288587092551228428935 : Int)/10^30)
theorem v382_pb_checked : Scalar.distance (sourceCoefficient 4 5 1 1) v382_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v382_pg : Scalar.QComplex := ((-93083359418365666191424 : Int)/10^30,(-756061812057957941508 : Int)/10^30)
theorem v382_pg_checked : Scalar.distance (sourceCoefficient 4 5 1 2) v382_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v382_mb : Scalar.QComplex := ((3132189832877706832815493 : Int)/10^30,(-431466152180417165390151310 : Int)/10^30)
theorem v382_mb_checked : Scalar.distance (sourceCoefficient 4 5 3 1) v382_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v382_mg : Scalar.QComplex := ((-93083977206468881114051 : Int)/10^30,(-675734783682424021623 : Int)/10^30)
theorem v382_mg_checked : Scalar.distance (sourceCoefficient 4 5 3 2) v382_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v382_upper : Scalar.QComplex := ((999979543565578671615854883694 : Int)/10^30,(6396284106959878793771058400 : Int)/10^30)
theorem v382_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 5 5) 1) 14) v382_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material382 : Material (4 : Basis) (5 : Basis) where
  plus := ![v382_pa,v382_pb,v382_pg]
  minus := ![(Primitive.Addresses.material382 1).one,v382_mb,v382_mg]
  upper := v382_upper
  lower := (Primitive.Addresses.material382 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v382_pa_checked.trans (by decide +kernel)
    · exact v382_pb_checked.trans (by decide +kernel)
    · exact v382_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 5 Primitive.Addresses.material382
    · exact v382_mb_checked.trans (by decide +kernel)
    · exact v382_mg_checked.trans (by decide +kernel)
  upper_error := v382_upper_checked
  lower_error := reuse_lower_error 4 5 Primitive.Addresses.material382

def v383_pa : Scalar.QComplex := ((999990807922941219648457807754 : Int)/10^30,(4287664821704239573167204594 : Int)/10^30)
theorem v383_pa_checked : Scalar.distance (sourceCoefficient 4 6 1 0) v383_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v383_pb : Scalar.QComplex := ((1850026395420835352773359 : Int)/10^30,(-431472483686426632894862725 : Int)/10^30)
theorem v383_pb_checked : Scalar.distance (sourceCoefficient 4 6 1 1) v383_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v383_pg : Scalar.QComplex := ((-93085458696141093505346 : Int)/10^30,(-399122915432241737015 : Int)/10^30)
theorem v383_pg_checked : Scalar.distance (sourceCoefficient 4 6 1 2) v383_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v383_mb : Scalar.QComplex := ((1477684385949357588694424 : Int)/10^30,(-431473919518958842174961546 : Int)/10^30)
theorem v383_mb_checked : Scalar.distance (sourceCoefficient 4 6 3 1) v383_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v383_mg : Scalar.QComplex := ((-93085768461270794514770 : Int)/10^30,(-318794208379199711783 : Int)/10^30)
theorem v383_mg_checked : Scalar.distance (sourceCoefficient 4 6 3 2) v383_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v383_upper : Scalar.QComplex := ((999996718674608337734875452913 : Int)/10^30,(2561765019713596659520030318 : Int)/10^30)
theorem v383_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 6 5) 1) 14) v383_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material383 : Material (4 : Basis) (6 : Basis) where
  plus := ![v383_pa,v383_pb,v383_pg]
  minus := ![(Primitive.Addresses.material383 1).one,v383_mb,v383_mg]
  upper := v383_upper
  lower := (Primitive.Addresses.material383 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v383_pa_checked.trans (by decide +kernel)
    · exact v383_pb_checked.trans (by decide +kernel)
    · exact v383_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 6 Primitive.Addresses.material383
    · exact v383_mb_checked.trans (by decide +kernel)
    · exact v383_mg_checked.trans (by decide +kernel)
  upper_error := v383_upper_checked
  lower_error := reuse_lower_error 4 6 Primitive.Addresses.material383

def v384_pa : Scalar.QComplex := ((999991061091875627694956274508 : Int)/10^30,(4228207225842431923679042886 : Int)/10^30)
theorem v384_pa_checked : Scalar.distance (sourceCoefficient 4 7 1 0) v384_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v384_pb : Scalar.QComplex := ((1824371702418132964171496 : Int)/10^30,(-431472559664720331992819984 : Int)/10^30)
theorem v384_pb_checked : Scalar.distance (sourceCoefficient 4 7 1 1) v384_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v384_pg : Scalar.QComplex := ((-93085478675167285691667 : Int)/10^30,(-393588211804208078115 : Int)/10^30)
theorem v384_pg_checked : Scalar.distance (sourceCoefficient 4 7 1 2) v384_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v384_mb : Scalar.QComplex := ((1452029636933224355388902 : Int)/10^30,(-431473973358379634230360136 : Int)/10^30)
theorem v384_mb_checked : Scalar.distance (sourceCoefficient 4 7 3 1) v384_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v384_mg : Scalar.QComplex := ((-93085783664089590401435 : Int)/10^30,(-313259489570989380131 : Int)/10^30)
theorem v384_mg_checked : Scalar.distance (sourceCoefficient 4 7 3 2) v384_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v384_upper : Scalar.QComplex := ((999996869224749173874232819814 : Int)/10^30,(2502307075460280184389001031 : Int)/10^30)
theorem v384_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 7 5) 1) 14) v384_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material384 : Material (4 : Basis) (7 : Basis) where
  plus := ![v384_pa,v384_pb,v384_pg]
  minus := ![(Primitive.Addresses.material384 1).one,v384_mb,v384_mg]
  upper := v384_upper
  lower := (Primitive.Addresses.material384 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v384_pa_checked.trans (by decide +kernel)
    · exact v384_pb_checked.trans (by decide +kernel)
    · exact v384_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 7 Primitive.Addresses.material384
    · exact v384_mb_checked.trans (by decide +kernel)
    · exact v384_mg_checked.trans (by decide +kernel)
  upper_error := v384_upper_checked
  lower_error := reuse_lower_error 4 7 Primitive.Addresses.material384

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
