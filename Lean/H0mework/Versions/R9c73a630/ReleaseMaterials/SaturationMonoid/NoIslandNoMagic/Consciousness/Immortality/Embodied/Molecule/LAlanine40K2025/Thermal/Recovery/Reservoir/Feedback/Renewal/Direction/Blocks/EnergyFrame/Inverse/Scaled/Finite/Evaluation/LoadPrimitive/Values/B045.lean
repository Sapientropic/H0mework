import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B030

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v721_pa : Scalar.QComplex := ((999999675075900047237127685526 : Int)/10^30,(-806131561427695879117792702 : Int)/10^30)
theorem v721_pa_checked : Scalar.distance (sourceCoefficient 7 71 1 0) v721_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v721_pb : Scalar.QComplex := ((-347827575592310742031383 : Int)/10^30,(-431477291322933012563811908 : Int)/10^30)
theorem v721_pb_checked : Scalar.distance (sourceCoefficient 7 71 1 1) v721_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v721_pg : Scalar.QComplex := ((-93086389998769283659915 : Int)/10^30,(75039901299647726452 : Int)/10^30)
theorem v721_pg_checked : Scalar.distance (sourceCoefficient 7 71 1 2) v721_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v721_mb : Scalar.QComplex := ((-720172915476085304564569 : Int)/10^30,(-431476830504685802967123506 : Int)/10^30)
theorem v721_mb_checked : Scalar.distance (sourceCoefficient 7 71 3 1) v721_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v721_mg : Scalar.QComplex := ((-93086290582396879029786 : Int)/10^30,(155369235472426585918 : Int)/10^30)
theorem v721_mg_checked : Scalar.distance (sourceCoefficient 7 71 3 2) v721_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v721_upper : Scalar.QComplex := ((999996794383908894986631764895 : Int)/10^30,(-2532039080708570577153724590 : Int)/10^30)
theorem v721_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 71 5) 1) 14) v721_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material721 : Material (7 : Basis) (71 : Basis) where
  plus := ![v721_pa,v721_pb,v721_pg]
  minus := ![(Primitive.Addresses.material721 1).one,v721_mb,v721_mg]
  upper := v721_upper
  lower := (Primitive.Addresses.material721 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v721_pa_checked.trans (by decide +kernel)
    · exact v721_pb_checked.trans (by decide +kernel)
    · exact v721_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 71 Primitive.Addresses.material721
    · exact v721_mb_checked.trans (by decide +kernel)
    · exact v721_mg_checked.trans (by decide +kernel)
  upper_error := v721_upper_checked
  lower_error := reuse_lower_error 7 71 Primitive.Addresses.material721

def v722_pa : Scalar.QComplex := ((999999653476661133620615207409 : Int)/10^30,(-832494178751019489963059745 : Int)/10^30)
theorem v722_pa_checked : Scalar.distance (sourceCoefficient 7 72 1 0) v722_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v722_pb : Scalar.QComplex := ((-359202446440517302845968 : Int)/10^30,(-431477277723903059246673223 : Int)/10^30)
theorem v722_pb_checked : Scalar.distance (sourceCoefficient 7 72 1 1) v722_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v722_pg : Scalar.QComplex := ((-93086387526552247529783 : Int)/10^30,(77493902590262125128 : Int)/10^30)
theorem v722_pg_checked : Scalar.distance (sourceCoefficient 7 72 1 2) v722_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v722_mb : Scalar.QComplex := ((-731547770353557219172789 : Int)/10^30,(-431476807089659676353422383 : Int)/10^30)
theorem v722_mb_checked : Scalar.distance (sourceCoefficient 7 72 3 1) v722_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v722_mg : Scalar.QComplex := ((-93086285992488173734097 : Int)/10^30,(157823233715892193040 : Int)/10^30)
theorem v722_mg_checked : Scalar.distance (sourceCoefficient 7 72 3 2) v722_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v722_upper : Scalar.QComplex := ((999996727285216248804137855459 : Int)/10^30,(-2558401621489545558221159941 : Int)/10^30)
theorem v722_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 72 5) 1) 14) v722_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material722 : Material (7 : Basis) (72 : Basis) where
  plus := ![v722_pa,v722_pb,v722_pg]
  minus := ![(Primitive.Addresses.material722 1).one,v722_mb,v722_mg]
  upper := v722_upper
  lower := (Primitive.Addresses.material722 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v722_pa_checked.trans (by decide +kernel)
    · exact v722_pb_checked.trans (by decide +kernel)
    · exact v722_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 72 Primitive.Addresses.material722
    · exact v722_mb_checked.trans (by decide +kernel)
    · exact v722_mg_checked.trans (by decide +kernel)
  upper_error := v722_upper_checked
  lower_error := reuse_lower_error 7 72 Primitive.Addresses.material722

def v723_pa : Scalar.QComplex := ((999999645565240795347921932783 : Int)/10^30,(-841943818069415854817711305 : Int)/10^30)
theorem v723_pa_checked : Scalar.distance (sourceCoefficient 7 73 1 0) v723_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v723_pb : Scalar.QComplex := ((-363279751189974450400697 : Int)/10^30,(-431477272752006773133273415 : Int)/10^30)
theorem v723_pb_checked : Scalar.distance (sourceCoefficient 7 73 1 1) v723_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v723_pg : Scalar.QComplex := ((-93086386622013908363463 : Int)/10^30,(78373535541129381493 : Int)/10^30)
theorem v723_pg_checked : Scalar.distance (sourceCoefficient 7 73 1 2) v723_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v723_mb : Scalar.QComplex := ((-735625069294324897452430 : Int)/10^30,(-431476798599234877711782767 : Int)/10^30)
theorem v723_mb_checked : Scalar.distance (sourceCoefficient 7 73 3 1) v723_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v723_mg : Scalar.QComplex := ((-93086284328866551967746 : Int)/10^30,(158702865558656052780 : Int)/10^30)
theorem v723_mg_checked : Scalar.distance (sourceCoefficient 7 73 3 2) v723_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v723_upper : Scalar.QComplex := ((999996703064587494692953481703 : Int)/10^30,(-2567851233079420405522213508 : Int)/10^30)
theorem v723_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 73 5) 1) 14) v723_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material723 : Material (7 : Basis) (73 : Basis) where
  plus := ![v723_pa,v723_pb,v723_pg]
  minus := ![(Primitive.Addresses.material723 1).one,v723_mb,v723_mg]
  upper := v723_upper
  lower := (Primitive.Addresses.material723 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v723_pa_checked.trans (by decide +kernel)
    · exact v723_pb_checked.trans (by decide +kernel)
    · exact v723_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 73 Primitive.Addresses.material723
    · exact v723_mb_checked.trans (by decide +kernel)
    · exact v723_mg_checked.trans (by decide +kernel)
  upper_error := v723_upper_checked
  lower_error := reuse_lower_error 7 73 Primitive.Addresses.material723

def v724_pa : Scalar.QComplex := ((999999636556176284651305274982 : Int)/10^30,(-852576984992724508987610810 : Int)/10^30)
theorem v724_pa_checked : Scalar.distance (sourceCoefficient 7 74 1 0) v724_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v724_pb : Scalar.QComplex := ((-367867721172838160620653 : Int)/10^30,(-431477267095975110202418641 : Int)/10^30)
theorem v724_pb_checked : Scalar.distance (sourceCoefficient 7 74 1 1) v724_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v724_pg : Scalar.QComplex := ((-93086385592590417072907 : Int)/10^30,(79363338816516249258 : Int)/10^30)
theorem v724_pg_checked : Scalar.distance (sourceCoefficient 7 74 1 2) v724_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v724_mb : Scalar.QComplex := ((-740213032687977115566023 : Int)/10^30,(-431476788983993860066022677 : Int)/10^30)
theorem v724_mb_checked : Scalar.distance (sourceCoefficient 7 74 3 1) v724_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v724_mg : Scalar.QComplex := ((-93086282445287796404406 : Int)/10^30,(159692667577147815403 : Int)/10^30)
theorem v724_mg_checked : Scalar.distance (sourceCoefficient 7 74 3 2) v724_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v724_upper : Scalar.QComplex := ((999996675703654925676889567505 : Int)/10^30,(-2578484368617047937438015239 : Int)/10^30)
theorem v724_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 74 5) 1) 14) v724_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material724 : Material (7 : Basis) (74 : Basis) where
  plus := ![v724_pa,v724_pb,v724_pg]
  minus := ![(Primitive.Addresses.material724 1).one,v724_mb,v724_mg]
  upper := v724_upper
  lower := (Primitive.Addresses.material724 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v724_pa_checked.trans (by decide +kernel)
    · exact v724_pb_checked.trans (by decide +kernel)
    · exact v724_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 74 Primitive.Addresses.material724
    · exact v724_mb_checked.trans (by decide +kernel)
    · exact v724_mg_checked.trans (by decide +kernel)
  upper_error := v724_upper_checked
  lower_error := reuse_lower_error 7 74 Primitive.Addresses.material724

def v725_pa : Scalar.QComplex := ((999999623815394337193338376367 : Int)/10^30,(-867392108455429622930406339 : Int)/10^30)
theorem v725_pa_checked : Scalar.distance (sourceCoefficient 7 75 1 0) v725_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v725_pb : Scalar.QComplex := ((-374260110318292891867813 : Int)/10^30,(-431477259107012017042851263 : Int)/10^30)
theorem v725_pb_checked : Scalar.distance (sourceCoefficient 7 75 1 1) v725_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v725_pg : Scalar.QComplex := ((-93086384137828916722275 : Int)/10^30,(80742425379860935229 : Int)/10^30)
theorem v725_pg_checked : Scalar.distance (sourceCoefficient 7 75 1 2) v725_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v725_mb : Scalar.QComplex := ((-746605412559137881488354 : Int)/10^30,(-431476775478689811554762849 : Int)/10^30)
theorem v725_mb_checked : Scalar.distance (sourceCoefficient 7 75 3 1) v725_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v725_mg : Scalar.QComplex := ((-93086279800437245314619 : Int)/10^30,(161071752371601891694 : Int)/10^30)
theorem v725_mg_checked : Scalar.distance (sourceCoefficient 7 75 3 2) v725_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v725_upper : Scalar.QComplex := ((999996637393332874989617408852 : Int)/10^30,(-2593299448024933153730284752 : Int)/10^30)
theorem v725_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 75 5) 1) 14) v725_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material725 : Material (7 : Basis) (75 : Basis) where
  plus := ![v725_pa,v725_pb,v725_pg]
  minus := ![(Primitive.Addresses.material725 1).one,v725_mb,v725_mg]
  upper := v725_upper
  lower := (Primitive.Addresses.material725 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v725_pa_checked.trans (by decide +kernel)
    · exact v725_pb_checked.trans (by decide +kernel)
    · exact v725_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 75 Primitive.Addresses.material725
    · exact v725_mb_checked.trans (by decide +kernel)
    · exact v725_mg_checked.trans (by decide +kernel)
  upper_error := v725_upper_checked
  lower_error := reuse_lower_error 7 75 Primitive.Addresses.material725

def v726_pa : Scalar.QComplex := ((999999612956295269250971790910 : Int)/10^30,(-879822288680315648159684463 : Int)/10^30)
theorem v726_pa_checked : Scalar.distance (sourceCoefficient 7 76 1 0) v726_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v726_pb : Scalar.QComplex := ((-379623450568839219945863 : Int)/10^30,(-431477252306697398125888398 : Int)/10^30)
theorem v726_pb_checked : Scalar.distance (sourceCoefficient 7 76 1 1) v726_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v726_pg : Scalar.QComplex := ((-93086382898865768547863 : Int)/10^30,(81899506145740550272 : Int)/10^30)
theorem v726_pg_checked : Scalar.distance (sourceCoefficient 7 76 1 2) v726_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v726_mb : Scalar.QComplex := ((-751968744944302276205185 : Int)/10^30,(-431476764050056644362150129 : Int)/10^30)
theorem v726_mb_checked : Scalar.distance (sourceCoefficient 7 76 3 1) v726_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v726_mg : Scalar.QComplex := ((-93086277562965970491873 : Int)/10^30,(162228831637478060351 : Int)/10^30)
theorem v726_mg_checked : Scalar.distance (sourceCoefficient 7 76 3 2) v726_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v726_upper : Scalar.QComplex := ((999996605080886569387661079621 : Int)/10^30,(-2605729590994706024034602258 : Int)/10^30)
theorem v726_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 76 5) 1) 14) v726_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material726 : Material (7 : Basis) (76 : Basis) where
  plus := ![v726_pa,v726_pb,v726_pg]
  minus := ![(Primitive.Addresses.material726 1).one,v726_mb,v726_mg]
  upper := v726_upper
  lower := (Primitive.Addresses.material726 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v726_pa_checked.trans (by decide +kernel)
    · exact v726_pb_checked.trans (by decide +kernel)
    · exact v726_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 76 Primitive.Addresses.material726
    · exact v726_mb_checked.trans (by decide +kernel)
    · exact v726_mg_checked.trans (by decide +kernel)
  upper_error := v726_upper_checked
  lower_error := reuse_lower_error 7 76 Primitive.Addresses.material726

def v727_pa : Scalar.QComplex := ((999999610420295889673109823333 : Int)/10^30,(-882699980994849645671090991 : Int)/10^30)
theorem v727_pa_checked : Scalar.distance (sourceCoefficient 7 77 1 0) v727_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v727_pb : Scalar.QComplex := ((-380865109387301679288534 : Int)/10^30,(-431477250719695346818333200 : Int)/10^30)
theorem v727_pb_checked : Scalar.distance (sourceCoefficient 7 77 1 1) v727_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v727_pg : Scalar.QComplex := ((-93086382609643266600106 : Int)/10^30,(82167380171155068590 : Int)/10^30)
theorem v727_pg_checked : Scalar.distance (sourceCoefficient 7 77 1 2) v727_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v727_mb : Scalar.QComplex := ((-753210401930927116463599 : Int)/10^30,(-431476761391559545872138320 : Int)/10^30)
theorem v727_mb_checked : Scalar.distance (sourceCoefficient 7 77 3 1) v727_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v727_mg : Scalar.QComplex := ((-93086277042580356900388 : Int)/10^30,(162496705313564843477 : Int)/10^30)
theorem v727_mg_checked : Scalar.distance (sourceCoefficient 7 77 3 2) v727_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v727_upper : Scalar.QComplex := ((999996597578255094204764348510 : Int)/10^30,(-2608607274646350491447886537 : Int)/10^30)
theorem v727_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 77 5) 1) 14) v727_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material727 : Material (7 : Basis) (77 : Basis) where
  plus := ![v727_pa,v727_pb,v727_pg]
  minus := ![(Primitive.Addresses.material727 1).one,v727_mb,v727_mg]
  upper := v727_upper
  lower := (Primitive.Addresses.material727 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v727_pa_checked.trans (by decide +kernel)
    · exact v727_pb_checked.trans (by decide +kernel)
    · exact v727_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 77 Primitive.Addresses.material727
    · exact v727_mb_checked.trans (by decide +kernel)
    · exact v727_mg_checked.trans (by decide +kernel)
  upper_error := v727_upper_checked
  lower_error := reuse_lower_error 7 77 Primitive.Addresses.material727

def v728_pa : Scalar.QComplex := ((999999595000310949829955018763 : Int)/10^30,(-899999563375222954462288036 : Int)/10^30)
theorem v728_pa_checked : Scalar.distance (sourceCoefficient 7 78 1 0) v728_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v728_pb : Scalar.QComplex := ((-388329485850623250001256 : Int)/10^30,(-431477241078840464176528215 : Int)/10^30)
theorem v728_pb_checked : Scalar.distance (sourceCoefficient 7 78 1 1) v728_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v728_pg : Scalar.QComplex := ((-93086380851994490880155 : Int)/10^30,(83777736052931807079 : Int)/10^30)
theorem v728_pg_checked : Scalar.distance (sourceCoefficient 7 78 1 2) v728_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v728_mb : Scalar.QComplex := ((-760674767295296635290204 : Int)/10^30,(-431476745309287548150906538 : Int)/10^30)
theorem v728_mb_checked : Scalar.distance (sourceCoefficient 7 78 3 1) v728_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v728_mg : Scalar.QComplex := ((-93086273895267637396638 : Int)/10^30,(164107059078960758396 : Int)/10^30)
theorem v728_mg_checked : Scalar.distance (sourceCoefficient 7 78 3 2) v728_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v728_upper : Scalar.QComplex := ((999996552300783337947509512678 : Int)/10^30,(-2625906804647532880307237228 : Int)/10^30)
theorem v728_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 78 5) 1) 14) v728_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material728 : Material (7 : Basis) (78 : Basis) where
  plus := ![v728_pa,v728_pb,v728_pg]
  minus := ![(Primitive.Addresses.material728 1).one,v728_mb,v728_mg]
  upper := v728_upper
  lower := (Primitive.Addresses.material728 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v728_pa_checked.trans (by decide +kernel)
    · exact v728_pb_checked.trans (by decide +kernel)
    · exact v728_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 78 Primitive.Addresses.material728
    · exact v728_mb_checked.trans (by decide +kernel)
    · exact v728_mg_checked.trans (by decide +kernel)
  upper_error := v728_upper_checked
  lower_error := reuse_lower_error 7 78 Primitive.Addresses.material728

def v729_pa : Scalar.QComplex := ((999999589965388511697724944006 : Int)/10^30,(-905576642172390581447484992 : Int)/10^30)
theorem v729_pa_checked : Scalar.distance (sourceCoefficient 7 79 1 0) v729_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v729_pb : Scalar.QComplex := ((-390735868517409636158920 : Int)/10^30,(-431477237934099654206501899 : Int)/10^30)
theorem v729_pb_checked : Scalar.distance (sourceCoefficient 7 79 1 1) v729_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v729_pg : Scalar.QComplex := ((-93086380278431751425608 : Int)/10^30,(84296886249165468553 : Int)/10^30)
theorem v729_pg_checked : Scalar.distance (sourceCoefficient 7 79 1 2) v729_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v729_mb : Scalar.QComplex := ((-763081146352307092346696 : Int)/10^30,(-431476740087948047127031959 : Int)/10^30)
theorem v729_mb_checked : Scalar.distance (sourceCoefficient 7 79 3 1) v729_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v729_mg : Scalar.QComplex := ((-93086272873701873812933 : Int)/10^30,(164626208586932263635 : Int)/10^30)
theorem v729_mg_checked : Scalar.distance (sourceCoefficient 7 79 3 2) v729_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v729_upper : Scalar.QComplex := ((999996537640336343465708517465 : Int)/10^30,(-2631483866448477404986429252 : Int)/10^30)
theorem v729_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 79 5) 1) 14) v729_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material729 : Material (7 : Basis) (79 : Basis) where
  plus := ![v729_pa,v729_pb,v729_pg]
  minus := ![(Primitive.Addresses.material729 1).one,v729_mb,v729_mg]
  upper := v729_upper
  lower := (Primitive.Addresses.material729 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v729_pa_checked.trans (by decide +kernel)
    · exact v729_pb_checked.trans (by decide +kernel)
    · exact v729_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 79 Primitive.Addresses.material729
    · exact v729_mb_checked.trans (by decide +kernel)
    · exact v729_mg_checked.trans (by decide +kernel)
  upper_error := v729_upper_checked
  lower_error := reuse_lower_error 7 79 Primitive.Addresses.material729

def v730_pa : Scalar.QComplex := ((999999582038099345494215339508 : Int)/10^30,(-914288590444429187504408742 : Int)/10^30)
theorem v730_pa_checked : Scalar.distance (sourceCoefficient 7 80 1 0) v730_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v730_pb : Scalar.QComplex := ((-394494876039364965530979 : Int)/10^30,(-431477232985895297645323237 : Int)/10^30)
theorem v730_pb_checked : Scalar.distance (sourceCoefficient 7 80 1 1) v730_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v730_pg : Scalar.QComplex := ((-93086379375710459035307 : Int)/10^30,(85107850160832513634 : Int)/10^30)
theorem v730_pg_checked : Scalar.distance (sourceCoefficient 7 80 1 2) v730_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v730_mb : Scalar.QComplex := ((-766840148204534625303194 : Int)/10^30,(-431476731895891340975129309 : Int)/10^30)
theorem v730_mb_checked : Scalar.distance (sourceCoefficient 7 80 3 1) v730_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v730_mg : Scalar.QComplex := ((-93086271271155586237095 : Int)/10^30,(165437171417632563245 : Int)/10^30)
theorem v730_mg_checked : Scalar.distance (sourceCoefficient 7 80 3 2) v730_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v730_upper : Scalar.QComplex := ((999996514677026608263001336955 : Int)/10^30,(-2640195788063310494362365606 : Int)/10^30)
theorem v730_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 80 5) 1) 14) v730_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material730 : Material (7 : Basis) (80 : Basis) where
  plus := ![v730_pa,v730_pb,v730_pg]
  minus := ![(Primitive.Addresses.material730 1).one,v730_mb,v730_mg]
  upper := v730_upper
  lower := (Primitive.Addresses.material730 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v730_pa_checked.trans (by decide +kernel)
    · exact v730_pb_checked.trans (by decide +kernel)
    · exact v730_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 80 Primitive.Addresses.material730
    · exact v730_mb_checked.trans (by decide +kernel)
    · exact v730_mg_checked.trans (by decide +kernel)
  upper_error := v730_upper_checked
  lower_error := reuse_lower_error 7 80 Primitive.Addresses.material730

def v731_pa : Scalar.QComplex := ((999999557710291134825773621488 : Int)/10^30,(-940520718596970560493317182 : Int)/10^30)
theorem v731_pa_checked : Scalar.distance (sourceCoefficient 7 81 1 0) v731_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v731_pb : Scalar.QComplex := ((-405813442452140912975336 : Int)/10^30,(-431477217822917113751398530 : Int)/10^30)
theorem v731_pb_checked : Scalar.distance (sourceCoefficient 7 81 1 1) v731_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v731_pg : Scalar.QComplex := ((-93086376607794895710427 : Int)/10^30,(87549704541084818837 : Int)/10^30)
theorem v731_pg_checked : Scalar.distance (sourceCoefficient 7 81 1 2) v731_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v731_mb : Scalar.QComplex := ((-778158697317923755717594 : Int)/10^30,(-431476706965505758033027377 : Int)/10^30)
theorem v731_mb_checked : Scalar.distance (sourceCoefficient 7 81 3 1) v731_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v731_mg : Scalar.QComplex := ((-93086266396030700414687 : Int)/10^30,(167879022500084415561 : Int)/10^30)
theorem v731_mg_checked : Scalar.distance (sourceCoefficient 7 81 3 2) v731_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v731_upper : Scalar.QComplex := ((999996445074981199797067540635 : Int)/10^30,(-2666427835158588456280198952 : Int)/10^30)
theorem v731_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 81 5) 1) 14) v731_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material731 : Material (7 : Basis) (81 : Basis) where
  plus := ![v731_pa,v731_pb,v731_pg]
  minus := ![(Primitive.Addresses.material731 1).one,v731_mb,v731_mg]
  upper := v731_upper
  lower := (Primitive.Addresses.material731 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v731_pa_checked.trans (by decide +kernel)
    · exact v731_pb_checked.trans (by decide +kernel)
    · exact v731_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 81 Primitive.Addresses.material731
    · exact v731_mb_checked.trans (by decide +kernel)
    · exact v731_mg_checked.trans (by decide +kernel)
  upper_error := v731_upper_checked
  lower_error := reuse_lower_error 7 81 Primitive.Addresses.material731

def v732_pa : Scalar.QComplex := ((999999548311867335730039497743 : Int)/10^30,(-950460973058005539100661687 : Int)/10^30)
theorem v732_pa_checked : Scalar.distance (sourceCoefficient 7 82 1 0) v732_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v732_pb : Scalar.QComplex := ((-410102435983295941715929 : Int)/10^30,(-431477211973714951326557027 : Int)/10^30)
theorem v732_pb_checked : Scalar.distance (sourceCoefficient 7 82 1 1) v732_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v732_pg : Scalar.QComplex := ((-93086375539412186711092 : Int)/10^30,(88475007036743348110 : Int)/10^30)
theorem v732_pg_checked : Scalar.distance (sourceCoefficient 7 82 1 2) v732_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v732_mb : Scalar.QComplex := ((-782447684204492448234844 : Int)/10^30,(-431476697415097525244552131 : Int)/10^30)
theorem v732_mb_checked : Scalar.distance (sourceCoefficient 7 82 3 1) v732_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v732_mg : Scalar.QComplex := ((-93086264529154009547141 : Int)/10^30,(168804323729244377593 : Int)/10^30)
theorem v732_mg_checked : Scalar.distance (sourceCoefficient 7 82 3 2) v732_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v732_upper : Scalar.QComplex := ((999996418520593971643634922883 : Int)/10^30,(-2676368058593955220596408115 : Int)/10^30)
theorem v732_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 82 5) 1) 14) v732_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material732 : Material (7 : Basis) (82 : Basis) where
  plus := ![v732_pa,v732_pb,v732_pg]
  minus := ![(Primitive.Addresses.material732 1).one,v732_mb,v732_mg]
  upper := v732_upper
  lower := (Primitive.Addresses.material732 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v732_pa_checked.trans (by decide +kernel)
    · exact v732_pb_checked.trans (by decide +kernel)
    · exact v732_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 82 Primitive.Addresses.material732
    · exact v732_mb_checked.trans (by decide +kernel)
    · exact v732_mg_checked.trans (by decide +kernel)
  upper_error := v732_upper_checked
  lower_error := reuse_lower_error 7 82 Primitive.Addresses.material732

def v733_pa : Scalar.QComplex := ((999999535323369095804204455678 : Int)/10^30,(-964029587660057393642398792 : Int)/10^30)
theorem v733_pa_checked : Scalar.distance (sourceCoefficient 7 83 1 0) v733_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v733_pb : Scalar.QComplex := ((-415956984243703888713608 : Int)/10^30,(-431477203897699594834950759 : Int)/10^30)
theorem v733_pb_checked : Scalar.distance (sourceCoefficient 7 83 1 1) v733_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v733_pg : Scalar.QComplex := ((-93086374063730897553853 : Int)/10^30,(89738060504607977454 : Int)/10^30)
theorem v733_pg_checked : Scalar.distance (sourceCoefficient 7 83 1 2) v733_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v733_mb : Scalar.QComplex := ((-788302223315746989386211 : Int)/10^30,(-431476684286873706155918727 : Int)/10^30)
theorem v733_mb_checked : Scalar.distance (sourceCoefficient 7 83 3 1) v733_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v733_mg : Scalar.QComplex := ((-93086261963515012902805 : Int)/10^30,(170067375453369986131 : Int)/10^30)
theorem v733_mg_checked : Scalar.distance (sourceCoefficient 7 83 3 2) v733_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v733_upper : Scalar.QComplex := ((999996382113917208519851950123 : Int)/10^30,(-2689936630570179852061031878 : Int)/10^30)
theorem v733_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 83 5) 1) 14) v733_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material733 : Material (7 : Basis) (83 : Basis) where
  plus := ![v733_pa,v733_pb,v733_pg]
  minus := ![(Primitive.Addresses.material733 1).one,v733_mb,v733_mg]
  upper := v733_upper
  lower := (Primitive.Addresses.material733 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v733_pa_checked.trans (by decide +kernel)
    · exact v733_pb_checked.trans (by decide +kernel)
    · exact v733_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 83 Primitive.Addresses.material733
    · exact v733_mb_checked.trans (by decide +kernel)
    · exact v733_mg_checked.trans (by decide +kernel)
  upper_error := v733_upper_checked
  lower_error := reuse_lower_error 7 83 Primitive.Addresses.material733

def v734_pa : Scalar.QComplex := ((999999500830901909482764200731 : Int)/10^30,(-999168627915851841122377287 : Int)/10^30)
theorem v734_pa_checked : Scalar.distance (sourceCoefficient 7 84 1 0) v734_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v734_pb : Scalar.QComplex := ((-431118679607330253731822 : Int)/10^30,(-431477182490677434150193084 : Int)/10^30)
theorem v734_pb_checked : Scalar.distance (sourceCoefficient 7 84 1 1) v734_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v734_pg : Scalar.QComplex := ((-93086370149178229695345 : Int)/10^30,(93009027166853725582 : Int)/10^30)
theorem v734_pg_checked : Scalar.distance (sourceCoefficient 7 84 1 2) v734_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v734_mb : Scalar.QComplex := ((-803463894560685258633828 : Int)/10^30,(-431476649795999274884626835 : Int)/10^30)
theorem v734_mb_checked : Scalar.distance (sourceCoefficient 7 84 3 1) v734_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v734_mg : Scalar.QComplex := ((-93086255226266891962813 : Int)/10^30,(173338337519602707889 : Int)/10^30)
theorem v734_mg_checked : Scalar.distance (sourceCoefficient 7 84 3 2) v734_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v734_upper : Scalar.QComplex := ((999996286974705702005665444893 : Int)/10^30,(-2725075558959632328749153994 : Int)/10^30)
theorem v734_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 84 5) 1) 14) v734_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material734 : Material (7 : Basis) (84 : Basis) where
  plus := ![v734_pa,v734_pb,v734_pg]
  minus := ![(Primitive.Addresses.material734 1).one,v734_mb,v734_mg]
  upper := v734_upper
  lower := (Primitive.Addresses.material734 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v734_pa_checked.trans (by decide +kernel)
    · exact v734_pb_checked.trans (by decide +kernel)
    · exact v734_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 84 Primitive.Addresses.material734
    · exact v734_mb_checked.trans (by decide +kernel)
    · exact v734_mg_checked.trans (by decide +kernel)
  upper_error := v734_upper_checked
  lower_error := reuse_lower_error 7 84 Primitive.Addresses.material734

def v735_pa : Scalar.QComplex := ((999999418714821546333858503785 : Int)/10^30,(-1078225402694109035932428868 : Int)/10^30)
theorem v735_pa_checked : Scalar.distance (sourceCoefficient 7 85 1 0) v735_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v735_pb : Scalar.QComplex := ((-465229874545904857863661 : Int)/10^30,(-431477131731665541429609543 : Int)/10^30)
theorem v735_pb_checked : Scalar.distance (sourceCoefficient 7 85 1 1) v735_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v735_pg : Scalar.QComplex := ((-93086360851888355959529 : Int)/10^30,(100368137257367045964 : Int)/10^30)
theorem v735_pg_checked : Scalar.distance (sourceCoefficient 7 85 1 2) v735_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v735_mb : Scalar.QComplex := ((-837575032995361866125256 : Int)/10^30,(-431476569600581361263570334 : Int)/10^30)
theorem v735_mb_checked : Scalar.distance (sourceCoefficient 7 85 3 1) v735_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v735_mg : Scalar.QComplex := ((-93086239578399913934699 : Int)/10^30,(180697436846840586984 : Int)/10^30)
theorem v735_mg_checked : Scalar.distance (sourceCoefficient 7 85 3 2) v735_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v735_upper : Scalar.QComplex := ((999996068413926348424002594730 : Int)/10^30,(-2804132074267204958286065823 : Int)/10^30)
theorem v735_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 85 5) 1) 14) v735_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material735 : Material (7 : Basis) (85 : Basis) where
  plus := ![v735_pa,v735_pb,v735_pg]
  minus := ![(Primitive.Addresses.material735 1).one,v735_mb,v735_mg]
  upper := v735_upper
  lower := (Primitive.Addresses.material735 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v735_pa_checked.trans (by decide +kernel)
    · exact v735_pb_checked.trans (by decide +kernel)
    · exact v735_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 85 Primitive.Addresses.material735
    · exact v735_mb_checked.trans (by decide +kernel)
    · exact v735_mg_checked.trans (by decide +kernel)
  upper_error := v735_upper_checked
  lower_error := reuse_lower_error 7 85 Primitive.Addresses.material735

def v736_pa : Scalar.QComplex := ((999999402882931928424005111419 : Int)/10^30,(-1092810038201680780745796630 : Int)/10^30)
theorem v736_pa_checked : Scalar.distance (sourceCoefficient 7 86 1 0) v736_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v736_pb : Scalar.QComplex := ((-471522811702570185960522 : Int)/10^30,(-431477121974634250588954539 : Int)/10^30)
theorem v736_pb_checked : Scalar.distance (sourceCoefficient 7 86 1 1) v736_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v736_pg : Scalar.QComplex := ((-93086359062536329490048 : Int)/10^30,(101725768345378241900 : Int)/10^30)
theorem v736_pg_checked : Scalar.distance (sourceCoefficient 7 86 1 2) v736_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v736_mb : Scalar.QComplex := ((-843867959389000525740817 : Int)/10^30,(-431476554413032360577771342 : Int)/10^30)
theorem v736_mb_checked : Scalar.distance (sourceCoefficient 7 86 3 1) v736_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v736_mg : Scalar.QComplex := ((-93086236617474070203472 : Int)/10^30,(182055065885213472628 : Int)/10^30)
theorem v736_mg_checked : Scalar.distance (sourceCoefficient 7 86 3 2) v736_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v736_upper : Scalar.QComplex := ((999996027410302531982855128274 : Int)/10^30,(-2818716660728270123500296987 : Int)/10^30)
theorem v736_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 86 5) 1) 14) v736_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material736 : Material (7 : Basis) (86 : Basis) where
  plus := ![v736_pa,v736_pb,v736_pg]
  minus := ![(Primitive.Addresses.material736 1).one,v736_mb,v736_mg]
  upper := v736_upper
  lower := (Primitive.Addresses.material736 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v736_pa_checked.trans (by decide +kernel)
    · exact v736_pb_checked.trans (by decide +kernel)
    · exact v736_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 86 Primitive.Addresses.material736
    · exact v736_mb_checked.trans (by decide +kernel)
    · exact v736_mg_checked.trans (by decide +kernel)
  upper_error := v736_upper_checked
  lower_error := reuse_lower_error 7 86 Primitive.Addresses.material736

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
