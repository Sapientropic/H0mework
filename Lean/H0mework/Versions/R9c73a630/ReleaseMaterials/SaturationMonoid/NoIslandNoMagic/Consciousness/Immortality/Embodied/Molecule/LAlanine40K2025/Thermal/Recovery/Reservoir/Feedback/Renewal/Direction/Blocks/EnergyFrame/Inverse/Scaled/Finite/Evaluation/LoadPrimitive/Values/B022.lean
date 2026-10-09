import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B014
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B015

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v353_pa : Scalar.QComplex := ((999995017891954368535463320776 : Int)/10^30,(3156610725107286764441918251 : Int)/10^30)
theorem v353_pa_checked : Scalar.distance (sourceCoefficient 3 69 1 0) v353_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v353_pb : Scalar.QComplex := ((1362000892747350333432513 : Int)/10^30,(-431473572676736380304327830 : Int)/10^30)
theorem v353_pb_checked : Scalar.distance (sourceCoefficient 3 69 1 1) v353_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v353_pg : Scalar.QComplex := ((-93085772110297611884800 : Int)/10^30,(-293837010525992441767 : Int)/10^30)
theorem v353_pg_checked : Scalar.distance (sourceCoefficient 3 69 1 2) v353_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v353_mb : Scalar.QComplex := ((989658125240480072849939 : Int)/10^30,(-431474587364834154215148216 : Int)/10^30)
theorem v353_mb_checked : Scalar.distance (sourceCoefficient 3 69 3 1) v353_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v353_mg : Scalar.QComplex := ((-93085991018316581516210 : Int)/10^30,(-213508072213403190944 : Int)/10^30)
theorem v353_mg_checked : Scalar.distance (sourceCoefficient 3 69 3 2) v353_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v353_upper : Scalar.QComplex := ((999998976540588932084185131282 : Int)/10^30,(1430705341664266495113023073 : Int)/10^30)
theorem v353_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 69 5) 1) 14) v353_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material353 : Material (3 : Basis) (69 : Basis) where
  plus := ![v353_pa,v353_pb,v353_pg]
  minus := ![(Primitive.Addresses.material353 1).one,v353_mb,v353_mg]
  upper := v353_upper
  lower := (Primitive.Addresses.material353 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v353_pa_checked.trans (by decide +kernel)
    · exact v353_pb_checked.trans (by decide +kernel)
    · exact v353_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 69 Primitive.Addresses.material353
    · exact v353_mb_checked.trans (by decide +kernel)
    · exact v353_mg_checked.trans (by decide +kernel)
  upper_error := v353_upper_checked
  lower_error := reuse_lower_error 3 69 Primitive.Addresses.material353

def v354_pa : Scalar.QComplex := ((999995062715457475347641408245 : Int)/10^30,(3142378829528777687840987443 : Int)/10^30)
theorem v354_pa_checked : Scalar.distance (sourceCoefficient 3 70 1 0) v354_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v354_pb : Scalar.QComplex := ((1355860143108106567993279 : Int)/10^30,(-431473581765474200929084400 : Int)/10^30)
theorem v354_pb_checked : Scalar.distance (sourceCoefficient 3 70 1 1) v354_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v354_pg : Scalar.QComplex := ((-93085775176923199035521 : Int)/10^30,(-292512213462268897909 : Int)/10^30)
theorem v354_pg_checked : Scalar.distance (sourceCoefficient 3 70 1 2) v354_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v354_mb : Scalar.QComplex := ((983517370044546646580675 : Int)/10^30,(-431474591154378221117092820 : Int)/10^30)
theorem v354_mb_checked : Scalar.distance (sourceCoefficient 3 70 3 1) v354_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v354_mg : Scalar.QComplex := ((-93085992941700827473475 : Int)/10^30,(-212183272996602374105 : Int)/10^30)
theorem v354_mg_checked : Scalar.distance (sourceCoefficient 3 70 3 2) v354_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v354_upper : Scalar.QComplex := ((999998996801064618528462133376 : Int)/10^30,(1416473389921194080888851308 : Int)/10^30)
theorem v354_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 70 5) 1) 14) v354_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material354 : Material (3 : Basis) (70 : Basis) where
  plus := ![v354_pa,v354_pb,v354_pg]
  minus := ![(Primitive.Addresses.material354 1).one,v354_mb,v354_mg]
  upper := v354_upper
  lower := (Primitive.Addresses.material354 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v354_pa_checked.trans (by decide +kernel)
    · exact v354_pb_checked.trans (by decide +kernel)
    · exact v354_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 70 Primitive.Addresses.material354
    · exact v354_mb_checked.trans (by decide +kernel)
    · exact v354_mg_checked.trans (by decide +kernel)
  upper_error := v354_upper_checked
  lower_error := reuse_lower_error 3 70 Primitive.Addresses.material354

def v355_pa : Scalar.QComplex := ((999995138757620760195418452509 : Int)/10^30,(3118086132037108984842112005 : Int)/10^30)
theorem v355_pa_checked : Scalar.distance (sourceCoefficient 3 71 1 0) v355_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v355_pb : Scalar.QComplex := ((1345378379387473856546378 : Int)/10^30,(-431473597010009830613392914 : Int)/10^30)
theorem v355_pb_checked : Scalar.distance (sourceCoefficient 3 71 1 1) v355_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v355_pg : Scalar.QComplex := ((-93085780360587058221917 : Int)/10^30,(-290250891812134673730 : Int)/10^30)
theorem v355_pg_checked : Scalar.distance (sourceCoefficient 3 71 1 2) v355_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v355_mb : Scalar.QComplex := ((973035597071405948572279 : Int)/10^30,(-431474597353618164771549347 : Int)/10^30)
theorem v355_mb_checked : Scalar.distance (sourceCoefficient 3 71 3 1) v355_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v355_mg : Scalar.QComplex := ((-93085996173944018625491 : Int)/10^30,(-209921947715193100852 : Int)/10^30)
theorem v355_mg_checked : Scalar.distance (sourceCoefficient 3 71 3 2) v355_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v355_upper : Scalar.QComplex := ((999999030916122593187560983137 : Int)/10^30,(1392180597368769332545098858 : Int)/10^30)
theorem v355_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 71 5) 1) 14) v355_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material355 : Material (3 : Basis) (71 : Basis) where
  plus := ![v355_pa,v355_pb,v355_pg]
  minus := ![(Primitive.Addresses.material355 1).one,v355_mb,v355_mg]
  upper := v355_upper
  lower := (Primitive.Addresses.material355 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v355_pa_checked.trans (by decide +kernel)
    · exact v355_pb_checked.trans (by decide +kernel)
    · exact v355_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 71 Primitive.Addresses.material355
    · exact v355_mb_checked.trans (by decide +kernel)
    · exact v355_mg_checked.trans (by decide +kernel)
  upper_error := v355_upper_checked
  lower_error := reuse_lower_error 3 71 Primitive.Addresses.material355

def v356_pa : Scalar.QComplex := ((999995220611067482695997643764 : Int)/10^30,(3091723632939406137536570786 : Int)/10^30)
theorem v356_pa_checked : Scalar.distance (sourceCoefficient 3 72 1 0) v356_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v356_pb : Scalar.QComplex := ((1334003542547005138307103 : Int)/10^30,(-431473613169286338682026184 : Int)/10^30)
theorem v356_pb_checked : Scalar.distance (sourceCoefficient 3 72 1 1) v356_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v356_pg : Scalar.QComplex := ((-93085785913399107064289 : Int)/10^30,(-287796899692511286544 : Int)/10^30)
theorem v356_pg_checked : Scalar.distance (sourceCoefficient 3 72 1 2) v356_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v356_mb : Scalar.QComplex := ((961660750521581002098488 : Int)/10^30,(-431474603696916766312209300 : Int)/10^30)
theorem v356_mb_checked : Scalar.distance (sourceCoefficient 3 72 3 1) v356_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v356_mg : Scalar.QComplex := ((-93085999609069324369412 : Int)/10^30,(-207467951717476424002 : Int)/10^30)
theorem v356_mg_checked : Scalar.distance (sourceCoefficient 3 72 3 2) v356_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v356_upper : Scalar.QComplex := ((999999067270165549195403197146 : Int)/10^30,(1365817996263288778233025013 : Int)/10^30)
theorem v356_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 72 5) 1) 14) v356_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material356 : Material (3 : Basis) (72 : Basis) where
  plus := ![v356_pa,v356_pb,v356_pg]
  minus := ![(Primitive.Addresses.material356 1).one,v356_mb,v356_mg]
  upper := v356_upper
  lower := (Primitive.Addresses.material356 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v356_pa_checked.trans (by decide +kernel)
    · exact v356_pb_checked.trans (by decide +kernel)
    · exact v356_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 72 Primitive.Addresses.material356
    · exact v356_mb_checked.trans (by decide +kernel)
    · exact v356_mg_checked.trans (by decide +kernel)
  upper_error := v356_upper_checked
  lower_error := reuse_lower_error 3 72 Primitive.Addresses.material356

def v357_pa : Scalar.QComplex := ((999995249782103265438573867460 : Int)/10^30,(3082274035334797481728860802 : Int)/10^30)
theorem v357_pa_checked : Scalar.distance (sourceCoefficient 3 73 1 0) v357_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v357_pb : Scalar.QComplex := ((1329926249796567411576200 : Int)/10^30,(-431473618864209135711914116 : Int)/10^30)
theorem v357_pb_checked : Scalar.distance (sourceCoefficient 3 73 1 1) v357_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v357_pg : Scalar.QComplex := ((-93085787885420086801645 : Int)/10^30,(-286917269977463505154 : Int)/10^30)
theorem v357_pg_checked : Scalar.distance (sourceCoefficient 3 73 1 2) v357_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v357_mb : Scalar.QComplex := ((957583454374843823804338 : Int)/10^30,(-431474605873317433682959454 : Int)/10^30)
theorem v357_mb_checked : Scalar.distance (sourceCoefficient 3 73 3 1) v357_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v357_mg : Scalar.QComplex := ((-93086000822008742798708 : Int)/10^30,(-206588320628189697603 : Int)/10^30)
theorem v357_mg_checked : Scalar.distance (sourceCoefficient 3 73 3 2) v357_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v357_upper : Scalar.QComplex := ((999999080132009680350447913504 : Int)/10^30,(1356368362386184341460248179 : Int)/10^30)
theorem v357_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 73 5) 1) 14) v357_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material357 : Material (3 : Basis) (73 : Basis) where
  plus := ![v357_pa,v357_pb,v357_pg]
  minus := ![(Primitive.Addresses.material357 1).one,v357_mb,v357_mg]
  upper := v357_upper
  lower := (Primitive.Addresses.material357 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v357_pa_checked.trans (by decide +kernel)
    · exact v357_pb_checked.trans (by decide +kernel)
    · exact v357_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 73 Primitive.Addresses.material357
    · exact v357_mb_checked.trans (by decide +kernel)
    · exact v357_mg_checked.trans (by decide +kernel)
  upper_error := v357_upper_checked
  lower_error := reuse_lower_error 3 73 Primitive.Addresses.material357

def v358_pa : Scalar.QComplex := ((999995282499917458156775812215 : Int)/10^30,(3071640914930756951952038527 : Int)/10^30)
theorem v358_pa_checked : Scalar.distance (sourceCoefficient 3 74 1 0) v358_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v358_pb : Scalar.QComplex := ((1325338293195024937735132 : Int)/10^30,(-431473625210970971618693692 : Int)/10^30)
theorem v358_pb_checked : Scalar.distance (sourceCoefficient 3 74 1 1) v358_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v358_pg : Scalar.QComplex := ((-93085790092832929679712 : Int)/10^30,(-285927470310666522777 : Int)/10^30)
theorem v358_pg_checked : Scalar.distance (sourceCoefficient 3 74 1 2) v358_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v358_mb : Scalar.QComplex := ((952995494004637655847002 : Int)/10^30,(-431474608260876993163813992 : Int)/10^30)
theorem v358_mb_checked : Scalar.distance (sourceCoefficient 3 74 3 1) v358_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v358_mg : Scalar.QComplex := ((-93086002175268230232440 : Int)/10^30,(-205598519425042502034 : Int)/10^30)
theorem v358_mg_checked : Scalar.distance (sourceCoefficient 3 74 3 2) v358_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v358_upper : Scalar.QComplex := ((999999094497973955501545020015 : Int)/10^30,(1345735201350948439724007592 : Int)/10^30)
theorem v358_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 74 5) 1) 14) v358_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material358 : Material (3 : Basis) (74 : Basis) where
  plus := ![v358_pa,v358_pb,v358_pg]
  minus := ![(Primitive.Addresses.material358 1).one,v358_mb,v358_mg]
  upper := v358_upper
  lower := (Primitive.Addresses.material358 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v358_pa_checked.trans (by decide +kernel)
    · exact v358_pb_checked.trans (by decide +kernel)
    · exact v358_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 74 Primitive.Addresses.material358
    · exact v358_mb_checked.trans (by decide +kernel)
    · exact v358_mg_checked.trans (by decide +kernel)
  upper_error := v358_upper_checked
  lower_error := reuse_lower_error 3 74 Primitive.Addresses.material358

def v359_pa : Scalar.QComplex := ((999995327896930167446778589161 : Int)/10^30,(3056825855543297269179703178 : Int)/10^30)
theorem v359_pa_checked : Scalar.distance (sourceCoefficient 3 75 1 0) v359_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v359_pb : Scalar.QComplex := ((1318945922480888249981130 : Int)/10^30,(-431473633945423572992114476 : Int)/10^30)
theorem v359_pb_checked : Scalar.distance (sourceCoefficient 3 75 1 1) v359_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v359_pg : Scalar.QComplex := ((-93085793147934881443678 : Int)/10^30,(-284548388717762886837 : Int)/10^30)
theorem v359_pg_checked : Scalar.distance (sourceCoefficient 3 75 1 2) v359_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v359_mb : Scalar.QComplex := ((946603118133233520896781 : Int)/10^30,(-431474611478998317690937183 : Int)/10^30)
theorem v359_mb_checked : Scalar.distance (sourceCoefficient 3 75 3 1) v359_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v359_mg : Scalar.QComplex := ((-93086004040283741295742 : Int)/10^30,(-204219435709218582586 : Int)/10^30)
theorem v359_mg_checked : Scalar.distance (sourceCoefficient 3 75 3 2) v359_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v359_upper : Scalar.QComplex := ((999999114325470560207199748807 : Int)/10^30,(1330920085677653864035258110 : Int)/10^30)
theorem v359_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 75 5) 1) 14) v359_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material359 : Material (3 : Basis) (75 : Basis) where
  plus := ![v359_pa,v359_pb,v359_pg]
  minus := ![(Primitive.Addresses.material359 1).one,v359_mb,v359_mg]
  upper := v359_upper
  lower := (Primitive.Addresses.material359 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v359_pa_checked.trans (by decide +kernel)
    · exact v359_pb_checked.trans (by decide +kernel)
    · exact v359_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 75 Primitive.Addresses.material359
    · exact v359_mb_checked.trans (by decide +kernel)
    · exact v359_mg_checked.trans (by decide +kernel)
  upper_error := v359_upper_checked
  lower_error := reuse_lower_error 3 75 Primitive.Addresses.material359

def v360_pa : Scalar.QComplex := ((999995365816586578403232963611 : Int)/10^30,(3044395728414307886267515544 : Int)/10^30)
theorem v360_pa_checked : Scalar.distance (sourceCoefficient 3 76 1 0) v360_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v360_pb : Scalar.QComplex := ((1313582597503437339469894 : Int)/10^30,(-431473641176384181789671773 : Int)/10^30)
theorem v360_pb_checked : Scalar.distance (sourceCoefficient 3 76 1 1) v360_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v360_pg : Scalar.QComplex := ((-93085795692836029193274 : Int)/10^30,(-283391312070634892255 : Int)/10^30)
theorem v360_pg_checked : Scalar.distance (sourceCoefficient 3 76 1 2) v360_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v360_mb : Scalar.QComplex := ((941239788912800280535043 : Int)/10^30,(-431474614081648333721287068 : Int)/10^30)
theorem v360_mb_checked : Scalar.distance (sourceCoefficient 3 76 3 1) v360_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v360_mg : Scalar.QComplex := ((-93086005586678907788543 : Int)/10^30,(-203062357296788032330 : Int)/10^30)
theorem v360_mg_checked : Scalar.distance (sourceCoefficient 3 76 3 2) v360_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v360_upper : Scalar.QComplex := ((999999130791798721978516208491 : Int)/10^30,(1318489911615991773497181952 : Int)/10^30)
theorem v360_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 76 5) 1) 14) v360_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material360 : Material (3 : Basis) (76 : Basis) where
  plus := ![v360_pa,v360_pb,v360_pg]
  minus := ![(Primitive.Addresses.material360 1).one,v360_mb,v360_mg]
  upper := v360_upper
  lower := (Primitive.Addresses.material360 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v360_pa_checked.trans (by decide +kernel)
    · exact v360_pb_checked.trans (by decide +kernel)
    · exact v360_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 76 Primitive.Addresses.material360
    · exact v360_mb_checked.trans (by decide +kernel)
    · exact v360_mg_checked.trans (by decide +kernel)
  upper_error := v360_upper_checked
  lower_error := reuse_lower_error 3 76 Primitive.Addresses.material360

def v361_pa : Scalar.QComplex := ((999995374573283629822760875612 : Int)/10^30,(3041518048305491473965998434 : Int)/10^30)
theorem v361_pa_checked : Scalar.distance (sourceCoefficient 3 77 1 0) v361_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v361_pb : Scalar.QComplex := ((1312340942195963466630363 : Int)/10^30,(-431473642837741572356604385 : Int)/10^30)
theorem v361_pb_checked : Scalar.distance (sourceCoefficient 3 77 1 1) v361_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v361_pg : Scalar.QComplex := ((-93085796279610265720993 : Int)/10^30,(-283123438992041539098 : Int)/10^30)
theorem v361_pg_checked : Scalar.distance (sourceCoefficient 3 77 1 2) v361_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v361_mb : Scalar.QComplex := ((939998132633974821818901 : Int)/10^30,(-431474614671512497418106594 : Int)/10^30)
theorem v361_mb_checked : Scalar.distance (sourceCoefficient 3 77 3 1) v361_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v361_mg : Scalar.QComplex := ((-93086005942290523562935 : Int)/10^30,(-202794483811576329945 : Int)/10^30)
theorem v361_mg_checked : Scalar.distance (sourceCoefficient 3 77 3 2) v361_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v361_upper : Scalar.QComplex := ((999999134581867924609466715658 : Int)/10^30,(1315612220679877137827268710 : Int)/10^30)
theorem v361_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 77 5) 1) 14) v361_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material361 : Material (3 : Basis) (77 : Basis) where
  plus := ![v361_pa,v361_pb,v361_pg]
  minus := ![(Primitive.Addresses.material361 1).one,v361_mb,v361_mg]
  upper := v361_upper
  lower := (Primitive.Addresses.material361 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v361_pa_checked.trans (by decide +kernel)
    · exact v361_pb_checked.trans (by decide +kernel)
    · exact v361_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 77 Primitive.Addresses.material361
    · exact v361_mb_checked.trans (by decide +kernel)
    · exact v361_mg_checked.trans (by decide +kernel)
  upper_error := v361_upper_checked
  lower_error := reuse_lower_error 3 77 Primitive.Addresses.material361

def v362_pa : Scalar.QComplex := ((999995427040659366119697058699 : Int)/10^30,(3024218538616319889586208064 : Int)/10^30)
theorem v362_pa_checked : Scalar.distance (sourceCoefficient 3 78 1 0) v362_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v362_pb : Scalar.QComplex := ((1304876586642348660096444 : Int)/10^30,(-431473652724777922615406091 : Int)/10^30)
theorem v362_pb_checked : Scalar.distance (sourceCoefficient 3 78 1 1) v362_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v362_pg : Scalar.QComplex := ((-93085799788117954221457 : Int)/10^30,(-281513088749062124853 : Int)/10^30)
theorem v362_pg_checked : Scalar.distance (sourceCoefficient 3 78 1 2) v362_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v362_mb : Scalar.QComplex := ((932533771327613651110849 : Int)/10^30,(-431474618117142505606306029 : Int)/10^30)
theorem v362_mb_checked : Scalar.distance (sourceCoefficient 3 78 3 1) v362_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v362_mg : Scalar.QComplex := ((-93086008061137173477002 : Int)/10^30,(-201184131140519789947 : Int)/10^30)
theorem v362_mg_checked : Scalar.distance (sourceCoefficient 3 78 3 2) v362_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v362_upper : Scalar.QComplex := ((999999157191781192662867354619 : Int)/10^30,(1298312646202362374606935415 : Int)/10^30)
theorem v362_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 78 5) 1) 14) v362_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material362 : Material (3 : Basis) (78 : Basis) where
  plus := ![v362_pa,v362_pb,v362_pg]
  minus := ![(Primitive.Addresses.material362 1).one,v362_mb,v362_mg]
  upper := v362_upper
  lower := (Primitive.Addresses.material362 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v362_pa_checked.trans (by decide +kernel)
    · exact v362_pb_checked.trans (by decide +kernel)
    · exact v362_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 78 Primitive.Addresses.material362
    · exact v362_mb_checked.trans (by decide +kernel)
    · exact v362_mg_checked.trans (by decide +kernel)
  upper_error := v362_upper_checked
  lower_error := reuse_lower_error 3 78 Primitive.Addresses.material362

def v363_pa : Scalar.QComplex := ((999995443891419483506428143335 : Int)/10^30,(3018641483003172022713392893 : Int)/10^30)
theorem v363_pa_checked : Scalar.distance (sourceCoefficient 3 79 1 0) v363_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v363_pb : Scalar.QComplex := ((1302470210644471776986633 : Int)/10^30,(-431473655875483292146648546 : Int)/10^30)
theorem v363_pb_checked : Scalar.distance (sourceCoefficient 3 79 1 1) v363_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v363_pg : Scalar.QComplex := ((-93085800912270769100323 : Int)/10^30,(-280993940351257765115 : Int)/10^30)
theorem v363_pg_checked : Scalar.distance (sourceCoefficient 3 79 1 2) v363_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v363_mb : Scalar.QComplex := ((930127393506823697423383 : Int)/10^30,(-431474619191252594969916084 : Int)/10^30)
theorem v363_mb_checked : Scalar.distance (sourceCoefficient 3 79 3 1) v363_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v363_mg : Scalar.QComplex := ((-93086008737287884053108 : Int)/10^30,(-200664981965924855689 : Int)/10^30)
theorem v363_mg_checked : Scalar.distance (sourceCoefficient 3 79 3 2) v363_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v363_upper : Scalar.QComplex := ((999999164417024171061602051171 : Int)/10^30,(1292735569812700442952275998 : Int)/10^30)
theorem v363_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 79 5) 1) 14) v363_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material363 : Material (3 : Basis) (79 : Basis) where
  plus := ![v363_pa,v363_pb,v363_pg]
  minus := ![(Primitive.Addresses.material363 1).one,v363_mb,v363_mg]
  upper := v363_upper
  lower := (Primitive.Addresses.material363 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v363_pa_checked.trans (by decide +kernel)
    · exact v363_pb_checked.trans (by decide +kernel)
    · exact v363_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 79 Primitive.Addresses.material363
    · exact v363_mb_checked.trans (by decide +kernel)
    · exact v363_mg_checked.trans (by decide +kernel)
  upper_error := v363_upper_checked
  lower_error := reuse_lower_error 3 79 Primitive.Addresses.material363

def v364_pa : Scalar.QComplex := ((999995470151729942326184934154 : Int)/10^30,(3009929570702609959265237781 : Int)/10^30)
theorem v364_pa_checked : Scalar.distance (sourceCoefficient 3 80 1 0) v364_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v364_pb : Scalar.QComplex := ((1298711213469752236583723 : Int)/10^30,(-431473660761388149328904340 : Int)/10^30)
theorem v364_pb_checked : Scalar.distance (sourceCoefficient 3 80 1 1) v364_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v364_pg : Scalar.QComplex := ((-93085802661548990243354 : Int)/10^30,(-280182979229967784228 : Int)/10^30)
theorem v364_pg_checked : Scalar.distance (sourceCoefficient 3 80 1 2) v364_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v364_mb : Scalar.QComplex := ((926368393515434761064001 : Int)/10^30,(-431474620833310370071610300 : Int)/10^30)
theorem v364_mb_checked : Scalar.distance (sourceCoefficient 3 80 3 1) v364_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v364_mg : Scalar.QComplex := ((-93086009786742530519715 : Int)/10^30,(-199854019637044442732 : Int)/10^30)
theorem v364_mg_checked : Scalar.distance (sourceCoefficient 3 80 3 2) v364_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v364_upper : Scalar.QComplex := ((999999175641325225973683033753 : Int)/10^30,(1284023625164594842916737178 : Int)/10^30)
theorem v364_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 80 5) 1) 14) v364_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material364 : Material (3 : Basis) (80 : Basis) where
  plus := ![v364_pa,v364_pb,v364_pg]
  minus := ![(Primitive.Addresses.material364 1).one,v364_mb,v364_mg]
  upper := v364_upper
  lower := (Primitive.Addresses.material364 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v364_pa_checked.trans (by decide +kernel)
    · exact v364_pb_checked.trans (by decide +kernel)
    · exact v364_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 80 Primitive.Addresses.material364
    · exact v364_mb_checked.trans (by decide +kernel)
    · exact v364_mg_checked.trans (by decide +kernel)
  upper_error := v364_upper_checked
  lower_error := reuse_lower_error 3 80 Primitive.Addresses.material364

def v365_pa : Scalar.QComplex := ((999995548764561107859060483121 : Int)/10^30,(2983697549063468569199664657 : Int)/10^30)
theorem v365_pa_checked : Scalar.distance (sourceCoefficient 3 81 1 0) v365_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v365_pb : Scalar.QComplex := ((1287392677695675023870200 : Int)/10^30,(-431473675209423606970552911 : Int)/10^30)
theorem v365_pb_checked : Scalar.distance (sourceCoefficient 3 81 1 1) v365_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v365_pg : Scalar.QComplex := ((-93085807878941746777040 : Int)/10^30,(-277741133112165948544 : Int)/10^30)
theorem v365_pg_checked : Scalar.distance (sourceCoefficient 3 81 1 2) v365_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v365_mb : Scalar.QComplex := ((915049849487761815095159 : Int)/10^30,(-431474625513953842948505032 : Int)/10^30)
theorem v365_mb_checked : Scalar.distance (sourceCoefficient 3 81 3 1) v365_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v365_mg : Scalar.QComplex := ((-93086012896930121383266 : Int)/10^30,(-197412169926078548345 : Int)/10^30)
theorem v365_mg_checked : Scalar.distance (sourceCoefficient 3 81 3 2) v365_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v365_upper : Scalar.QComplex := ((999999208979949708184522949444 : Int)/10^30,(1257791506916353363255707332 : Int)/10^30)
theorem v365_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 81 5) 1) 14) v365_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material365 : Material (3 : Basis) (81 : Basis) where
  plus := ![v365_pa,v365_pb,v365_pg]
  minus := ![(Primitive.Addresses.material365 1).one,v365_mb,v365_mg]
  upper := v365_upper
  lower := (Primitive.Addresses.material365 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v365_pa_checked.trans (by decide +kernel)
    · exact v365_pb_checked.trans (by decide +kernel)
    · exact v365_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 81 Primitive.Addresses.material365
    · exact v365_mb_checked.trans (by decide +kernel)
    · exact v365_mg_checked.trans (by decide +kernel)
  upper_error := v365_upper_checked
  lower_error := reuse_lower_error 3 81 Primitive.Addresses.material365

def v366_pa : Scalar.QComplex := ((999995578373883083075934898518 : Int)/10^30,(2973757334258518533896600952 : Int)/10^30)
theorem v366_pa_checked : Scalar.distance (sourceCoefficient 3 82 1 0) v366_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v366_pb : Scalar.QComplex := ((1283103695571636873782458 : Int)/10^30,(-431473680580851954039071205 : Int)/10^30)
theorem v366_pb_checked : Scalar.distance (sourceCoefficient 3 82 1 1) v366_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v366_pg : Scalar.QComplex := ((-93085809836466751100205 : Int)/10^30,(-276815833692706580620 : Int)/10^30)
theorem v366_pg_checked : Scalar.distance (sourceCoefficient 3 82 1 2) v366_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v366_mb : Scalar.QComplex := ((910760864325406982585406 : Int)/10^30,(-431474627184181785527951555 : Int)/10^30)
theorem v366_mb_checked : Scalar.distance (sourceCoefficient 3 82 3 1) v366_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v366_mg : Scalar.QComplex := ((-93086014055962671775817 : Int)/10^30,(-196486869161894527481 : Int)/10^30)
theorem v366_mg_checked : Scalar.distance (sourceCoefficient 3 82 3 2) v366_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v366_upper : Scalar.QComplex := ((999999221433318599693579950680 : Int)/10^30,(1247851255813182027753432725 : Int)/10^30)
theorem v366_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 82 5) 1) 14) v366_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material366 : Material (3 : Basis) (82 : Basis) where
  plus := ![v366_pa,v366_pb,v366_pg]
  minus := ![(Primitive.Addresses.material366 1).one,v366_mb,v366_mg]
  upper := v366_upper
  lower := (Primitive.Addresses.material366 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v366_pa_checked.trans (by decide +kernel)
    · exact v366_pb_checked.trans (by decide +kernel)
    · exact v366_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 82 Primitive.Addresses.material366
    · exact v366_mb_checked.trans (by decide +kernel)
    · exact v366_mg_checked.trans (by decide +kernel)
  upper_error := v366_upper_checked
  lower_error := reuse_lower_error 3 82 Primitive.Addresses.material366

def v367_pa : Scalar.QComplex := ((999995618631615428925748675214 : Int)/10^30,(2960188773161810906016599889 : Int)/10^30)
theorem v367_pa_checked : Scalar.distance (sourceCoefficient 3 83 1 0) v367_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v367_pb : Scalar.QComplex := ((1277249162702100311239617 : Int)/10^30,(-431473687821186287578871219 : Int)/10^30)
theorem v367_pb_checked : Scalar.distance (sourceCoefficient 3 83 1 1) v367_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v367_pg : Scalar.QComplex := ((-93085812491200483475696 : Int)/10^30,(-275552784375354874844 : Int)/10^30)
theorem v367_pg_checked : Scalar.distance (sourceCoefficient 3 83 1 2) v367_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v367_mb : Scalar.QComplex := ((904906327387698135449574 : Int)/10^30,(-431474629372315235122568744 : Int)/10^30)
theorem v367_mb_checked : Scalar.distance (sourceCoefficient 3 83 3 1) v367_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v367_mg : Scalar.QComplex := ((-93086015620740740427650 : Int)/10^30,(-195223818023918160488 : Int)/10^30)
theorem v367_mg_checked : Scalar.distance (sourceCoefficient 3 83 3 2) v367_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v367_upper : Scalar.QComplex := ((999999238272885463709898207114 : Int)/10^30,(1234282645444058402281985188 : Int)/10^30)
theorem v367_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 83 5) 1) 14) v367_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material367 : Material (3 : Basis) (83 : Basis) where
  plus := ![v367_pa,v367_pb,v367_pg]
  minus := ![(Primitive.Addresses.material367 1).one,v367_mb,v367_mg]
  upper := v367_upper
  lower := (Primitive.Addresses.material367 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v367_pa_checked.trans (by decide +kernel)
    · exact v367_pb_checked.trans (by decide +kernel)
    · exact v367_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 83 Primitive.Addresses.material367
    · exact v367_mb_checked.trans (by decide +kernel)
    · exact v367_mg_checked.trans (by decide +kernel)
  upper_error := v367_upper_checked
  lower_error := reuse_lower_error 3 83 Primitive.Addresses.material367

def v368_pa : Scalar.QComplex := ((999995722032484025509918124496 : Int)/10^30,(2925049868112151080562257280 : Int)/10^30)
theorem v368_pa_checked : Scalar.distance (sourceCoefficient 3 84 1 0) v368_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v368_pb : Scalar.QComplex := ((1262087506230666301935757 : Int)/10^30,(-431473706079366605698655691 : Int)/10^30)
theorem v368_pb_checked : Scalar.distance (sourceCoefficient 3 84 1 1) v368_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v368_pg : Scalar.QComplex := ((-93085819273305472387762 : Int)/10^30,(-272281828201309938499 : Int)/10^30)
theorem v368_pg_checked : Scalar.distance (sourceCoefficient 3 84 1 2) v368_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v368_mb : Scalar.QComplex := ((889744660805654455770657 : Int)/10^30,(-431474634546662075698510495 : Int)/10^30)
theorem v368_mb_checked : Scalar.distance (sourceCoefficient 3 84 3 1) v368_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v368_mg : Scalar.QComplex := ((-93086019580155344248655 : Int)/10^30,(-191952857215148547061 : Int)/10^30)
theorem v368_mg_checked : Scalar.distance (sourceCoefficient 3 84 3 2) v368_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v368_upper : Scalar.QComplex := ((999999281027037717698314741511 : Int)/10^30,(1199143614269151198372029732 : Int)/10^30)
theorem v368_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 84 5) 1) 14) v368_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material368 : Material (3 : Basis) (84 : Basis) where
  plus := ![v368_pa,v368_pb,v368_pg]
  minus := ![(Primitive.Addresses.material368 1).one,v368_mb,v368_mg]
  upper := v368_upper
  lower := (Primitive.Addresses.material368 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v368_pa_checked.trans (by decide +kernel)
    · exact v368_pb_checked.trans (by decide +kernel)
    · exact v368_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 84 Primitive.Addresses.material368
    · exact v368_mb_checked.trans (by decide +kernel)
    · exact v368_mg_checked.trans (by decide +kernel)
  upper_error := v368_upper_checked
  lower_error := reuse_lower_error 3 84 Primitive.Addresses.material368

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
