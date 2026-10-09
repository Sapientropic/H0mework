import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B050
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B051

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1217_pa : Scalar.QComplex := ((999999840228022157634090406371 : Int)/10^30,(-565282168618157382901627060 : Int)/10^30)
theorem v1217_pa_checked : Scalar.distance (sourceCoefficient 13 48 1 0) v1217_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1217_pb : Scalar.QComplex := ((-243906536883626078759978 : Int)/10^30,(-431477431015434600872550339 : Int)/10^30)
theorem v1217_pb_checked : Scalar.distance (sourceCoefficient 13 48 1 1) v1217_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1217_pg : Scalar.QComplex := ((-93086412754024395885958 : Int)/10^30,(52620097677696894747 : Int)/10^30)
theorem v1217_pg_checked : Scalar.distance (sourceCoefficient 13 48 1 2) v1217_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1217_mb : Scalar.QComplex := ((-616252036010290132622843 : Int)/10^30,(-431477059876311353130405709 : Int)/10^30)
theorem v1217_mb_checked : Scalar.distance (sourceCoefficient 13 48 3 1) v1217_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1217_mg : Scalar.QComplex := ((-93086332684924293706519 : Int)/10^30,(132949459835153581514 : Int)/10^30)
theorem v1217_mg_checked : Scalar.distance (sourceCoefficient 13 48 3 2) v1217_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1217_upper : Scalar.QComplex := ((999997375219987333725987439525 : Int)/10^30,(-2291190331653490792714141955 : Int)/10^30)
theorem v1217_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 48 5) 1) 14) v1217_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1217 : Material (13 : Basis) (48 : Basis) where
  plus := ![v1217_pa,v1217_pb,v1217_pg]
  minus := ![(Primitive.Addresses.material1217 1).one,v1217_mb,v1217_mg]
  upper := v1217_upper
  lower := (Primitive.Addresses.material1217 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1217_pa_checked.trans (by decide +kernel)
    · exact v1217_pb_checked.trans (by decide +kernel)
    · exact v1217_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 48 Primitive.Addresses.material1217
    · exact v1217_mb_checked.trans (by decide +kernel)
    · exact v1217_mg_checked.trans (by decide +kernel)
  upper_error := v1217_upper_checked
  lower_error := reuse_lower_error 13 48 Primitive.Addresses.material1217

def v1218_pa : Scalar.QComplex := ((999999827527271473913918275334 : Int)/10^30,(-587320549023555005237685145 : Int)/10^30)
theorem v1218_pa_checked : Scalar.distance (sourceCoefficient 13 49 1 0) v1218_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1218_pb : Scalar.QComplex := ((-253415601136326350997065 : Int)/10^30,(-431477423785631445630425127 : Int)/10^30)
theorem v1218_pb_checked : Scalar.distance (sourceCoefficient 13 49 1 1) v1218_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1218_pg : Scalar.QComplex := ((-93086411383016204660960 : Int)/10^30,(54671571669460716146 : Int)/10^30)
theorem v1218_pg_checked : Scalar.distance (sourceCoefficient 13 49 1 2) v1218_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1218_mb : Scalar.QComplex := ((-625761090483336693146941 : Int)/10^30,(-431477044440616712149803053 : Int)/10^30)
theorem v1218_mb_checked : Scalar.distance (sourceCoefficient 13 49 3 1) v1218_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1218_mg : Scalar.QComplex := ((-93086329543586953037078 : Int)/10^30,(135000931879941557676 : Int)/10^30)
theorem v1218_mg_checked : Scalar.distance (sourceCoefficient 13 49 3 2) v1218_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1218_upper : Scalar.QComplex := ((999997324483010292818381881717 : Int)/10^30,(-2313228657314966134227337941 : Int)/10^30)
theorem v1218_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 49 5) 1) 14) v1218_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1218 : Material (13 : Basis) (49 : Basis) where
  plus := ![v1218_pa,v1218_pb,v1218_pg]
  minus := ![(Primitive.Addresses.material1218 1).one,v1218_mb,v1218_mg]
  upper := v1218_upper
  lower := (Primitive.Addresses.material1218 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1218_pa_checked.trans (by decide +kernel)
    · exact v1218_pb_checked.trans (by decide +kernel)
    · exact v1218_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 49 Primitive.Addresses.material1218
    · exact v1218_mb_checked.trans (by decide +kernel)
    · exact v1218_mg_checked.trans (by decide +kernel)
  upper_error := v1218_upper_checked
  lower_error := reuse_lower_error 13 49 Primitive.Addresses.material1218

def v1219_pa : Scalar.QComplex := ((999999826011439928438001763454 : Int)/10^30,(-589895829677668564459639834 : Int)/10^30)
theorem v1219_pa_checked : Scalar.distance (sourceCoefficient 13 50 1 0) v1219_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1219_pb : Scalar.QComplex := ((-254526776666835597604560 : Int)/10^30,(-431477422922564078508022321 : Int)/10^30)
theorem v1219_pb_checked : Scalar.distance (sourceCoefficient 13 50 1 1) v1219_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1219_pg : Scalar.QComplex := ((-93086411219365984845974 : Int)/10^30,(54911295331901739609 : Int)/10^30)
theorem v1219_pg_checked : Scalar.distance (sourceCoefficient 13 50 1 2) v1219_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1219_mb : Scalar.QComplex := ((-626872264855316239799975 : Int)/10^30,(-431477042618655229045463624 : Int)/10^30)
theorem v1219_mb_checked : Scalar.distance (sourceCoefficient 13 50 3 1) v1219_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1219_mg : Scalar.QComplex := ((-93086329173066070222906 : Int)/10^30,(135240655311899736531 : Int)/10^30)
theorem v1219_mg_checked : Scalar.distance (sourceCoefficient 13 50 3 2) v1219_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1219_upper : Scalar.QComplex := ((999997318522480223631429300729 : Int)/10^30,(-2315803931517313940535372040 : Int)/10^30)
theorem v1219_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 50 5) 1) 14) v1219_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1219 : Material (13 : Basis) (50 : Basis) where
  plus := ![v1219_pa,v1219_pb,v1219_pg]
  minus := ![(Primitive.Addresses.material1219 1).one,v1219_mb,v1219_mg]
  upper := v1219_upper
  lower := (Primitive.Addresses.material1219 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1219_pa_checked.trans (by decide +kernel)
    · exact v1219_pb_checked.trans (by decide +kernel)
    · exact v1219_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 50 Primitive.Addresses.material1219
    · exact v1219_mb_checked.trans (by decide +kernel)
    · exact v1219_mg_checked.trans (by decide +kernel)
  upper_error := v1219_upper_checked
  lower_error := reuse_lower_error 13 50 Primitive.Addresses.material1219

def v1220_pa : Scalar.QComplex := ((999999819282222653572055771536 : Int)/10^30,(-601195078185060360216036223 : Int)/10^30)
theorem v1220_pa_checked : Scalar.distance (sourceCoefficient 13 51 1 0) v1220_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1220_pb : Scalar.QComplex := ((-259402147583896034121826 : Int)/10^30,(-431477419090691752582931680 : Int)/10^30)
theorem v1220_pb_checked : Scalar.distance (sourceCoefficient 13 51 1 1) v1220_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1220_pg : Scalar.QComplex := ((-93086410492824866396012 : Int)/10^30,(55963101947727866055 : Int)/10^30)
theorem v1220_pg_checked : Scalar.distance (sourceCoefficient 13 51 1 2) v1220_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1220_mb : Scalar.QComplex := ((-631747630650320032287119 : Int)/10^30,(-431477034579558807033373722 : Int)/10^30)
theorem v1220_mb_checked : Scalar.distance (sourceCoefficient 13 51 3 1) v1220_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1220_mg : Scalar.QComplex := ((-93086327538863484450920 : Int)/10^30,(136292460909117926944 : Int)/10^30)
theorem v1220_mg_checked : Scalar.distance (sourceCoefficient 13 51 3 2) v1220_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1220_upper : Scalar.QComplex := ((999997292291795107203168078070 : Int)/10^30,(-2327103151581783840903139533 : Int)/10^30)
theorem v1220_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 51 5) 1) 14) v1220_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1220 : Material (13 : Basis) (51 : Basis) where
  plus := ![v1220_pa,v1220_pb,v1220_pg]
  minus := ![(Primitive.Addresses.material1220 1).one,v1220_mb,v1220_mg]
  upper := v1220_upper
  lower := (Primitive.Addresses.material1220 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1220_pa_checked.trans (by decide +kernel)
    · exact v1220_pb_checked.trans (by decide +kernel)
    · exact v1220_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 51 Primitive.Addresses.material1220
    · exact v1220_mb_checked.trans (by decide +kernel)
    · exact v1220_mg_checked.trans (by decide +kernel)
  upper_error := v1220_upper_checked
  lower_error := reuse_lower_error 13 51 Primitive.Addresses.material1220

def v1221_pa : Scalar.QComplex := ((999999804447403557136840109049 : Int)/10^30,(-625384005747595326392866073 : Int)/10^30)
theorem v1221_pa_checked : Scalar.distance (sourceCoefficient 13 52 1 0) v1221_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1221_pb : Scalar.QComplex := ((-269839124223799914862057 : Int)/10^30,(-431477410640663979550669571 : Int)/10^30)
theorem v1221_pb_checked : Scalar.distance (sourceCoefficient 13 52 1 1) v1221_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1221_pg : Scalar.QComplex := ((-93086408890865390571295 : Int)/10^30,(58214762656875958966 : Int)/10^30)
theorem v1221_pg_checked : Scalar.distance (sourceCoefficient 13 52 1 2) v1221_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1221_mb : Scalar.QComplex := ((-642184596112067123591182 : Int)/10^30,(-431477017122893404073853953 : Int)/10^30)
theorem v1221_mb_checked : Scalar.distance (sourceCoefficient 13 52 3 1) v1221_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1221_mg : Scalar.QComplex := ((-93086323993822824147910 : Int)/10^30,(138544119397450953800 : Int)/10^30)
theorem v1221_mg_checked : Scalar.distance (sourceCoefficient 13 52 3 2) v1221_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1221_upper : Scalar.QComplex := ((999997235709103534919767264900 : Int)/10^30,(-2351292017514200677543676392 : Int)/10^30)
theorem v1221_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 52 5) 1) 14) v1221_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1221 : Material (13 : Basis) (52 : Basis) where
  plus := ![v1221_pa,v1221_pb,v1221_pg]
  minus := ![(Primitive.Addresses.material1221 1).one,v1221_mb,v1221_mg]
  upper := v1221_upper
  lower := (Primitive.Addresses.material1221 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1221_pa_checked.trans (by decide +kernel)
    · exact v1221_pb_checked.trans (by decide +kernel)
    · exact v1221_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 52 Primitive.Addresses.material1221
    · exact v1221_mb_checked.trans (by decide +kernel)
    · exact v1221_mg_checked.trans (by decide +kernel)
  upper_error := v1221_upper_checked
  lower_error := reuse_lower_error 13 52 Primitive.Addresses.material1221

def v1222_pa : Scalar.QComplex := ((999999802124945574519130435709 : Int)/10^30,(-629086694896994761772029053 : Int)/10^30)
theorem v1222_pa_checked : Scalar.distance (sourceCoefficient 13 53 1 0) v1222_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1222_pb : Scalar.QComplex := ((-271436751060813054400581 : Int)/10^30,(-431477409317479840363227797 : Int)/10^30)
theorem v1222_pb_checked : Scalar.distance (sourceCoefficient 13 53 1 1) v1222_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1222_pg : Scalar.QComplex := ((-93086408640039669686011 : Int)/10^30,(58559432738644553058 : Int)/10^30)
theorem v1222_pg_checked : Scalar.distance (sourceCoefficient 13 53 1 2) v1222_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1222_mb : Scalar.QComplex := ((-643782221212362458438874 : Int)/10^30,(-431477014421029751667664922 : Int)/10^30)
theorem v1222_mb_checked : Scalar.distance (sourceCoefficient 13 53 3 1) v1222_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1222_mg : Scalar.QComplex := ((-93086323445562439454437 : Int)/10^30,(138888789134431823896 : Int)/10^30)
theorem v1222_mg_checked : Scalar.distance (sourceCoefficient 13 53 3 2) v1222_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1222_upper : Scalar.QComplex := ((999997226996143444802667189828 : Int)/10^30,(-2354994697140527787057511585 : Int)/10^30)
theorem v1222_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 53 5) 1) 14) v1222_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1222 : Material (13 : Basis) (53 : Basis) where
  plus := ![v1222_pa,v1222_pb,v1222_pg]
  minus := ![(Primitive.Addresses.material1222 1).one,v1222_mb,v1222_mg]
  upper := v1222_upper
  lower := (Primitive.Addresses.material1222 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1222_pa_checked.trans (by decide +kernel)
    · exact v1222_pb_checked.trans (by decide +kernel)
    · exact v1222_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 53 Primitive.Addresses.material1222
    · exact v1222_mb_checked.trans (by decide +kernel)
    · exact v1222_mg_checked.trans (by decide +kernel)
  upper_error := v1222_upper_checked
  lower_error := reuse_lower_error 13 53 Primitive.Addresses.material1222

def v1223_pa : Scalar.QComplex := ((999999800938936896613301342955 : Int)/10^30,(-630969164525071346583181328 : Int)/10^30)
theorem v1223_pa_checked : Scalar.distance (sourceCoefficient 13 54 1 0) v1223_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1223_pb : Scalar.QComplex := ((-272248994236296123017766 : Int)/10^30,(-431477408641740656500801247 : Int)/10^30)
theorem v1223_pb_checked : Scalar.distance (sourceCoefficient 13 54 1 1) v1223_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1223_pg : Scalar.QComplex := ((-93086408511947442441173 : Int)/10^30,(58734665099207843305 : Int)/10^30)
theorem v1223_pg_checked : Scalar.distance (sourceCoefficient 13 54 1 2) v1223_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1223_mb : Scalar.QComplex := ((-644594463502277789966559 : Int)/10^30,(-431477013044361541046564428 : Int)/10^30)
theorem v1223_mb_checked : Scalar.distance (sourceCoefficient 13 54 3 1) v1223_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1223_mg : Scalar.QComplex := ((-93086323166252624910619 : Int)/10^30,(139064021319210274738 : Int)/10^30)
theorem v1223_mg_checked : Scalar.distance (sourceCoefficient 13 54 3 2) v1223_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1223_upper : Scalar.QComplex := ((999997222561164731567887866513 : Int)/10^30,(-2356877161917943607065990606 : Int)/10^30)
theorem v1223_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 54 5) 1) 14) v1223_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1223 : Material (13 : Basis) (54 : Basis) where
  plus := ![v1223_pa,v1223_pb,v1223_pg]
  minus := ![(Primitive.Addresses.material1223 1).one,v1223_mb,v1223_mg]
  upper := v1223_upper
  lower := (Primitive.Addresses.material1223 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1223_pa_checked.trans (by decide +kernel)
    · exact v1223_pb_checked.trans (by decide +kernel)
    · exact v1223_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 54 Primitive.Addresses.material1223
    · exact v1223_mb_checked.trans (by decide +kernel)
    · exact v1223_mg_checked.trans (by decide +kernel)
  upper_error := v1223_upper_checked
  lower_error := reuse_lower_error 13 54 Primitive.Addresses.material1223

def v1224_pa : Scalar.QComplex := ((999999791139887982859074408432 : Int)/10^30,(-646312757426105166750495653 : Int)/10^30)
theorem v1224_pa_checked : Scalar.distance (sourceCoefficient 13 55 1 0) v1224_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1224_pb : Scalar.QComplex := ((-278869408382109388974737 : Int)/10^30,(-431477403057911118029330943 : Int)/10^30)
theorem v1224_pb_checked : Scalar.distance (sourceCoefficient 13 55 1 1) v1224_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1224_pg : Scalar.QComplex := ((-93086407453543942307123 : Int)/10^30,(60162945245829417268 : Int)/10^30)
theorem v1224_pg_checked : Scalar.distance (sourceCoefficient 13 55 1 2) v1224_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1224_mb : Scalar.QComplex := ((-651214870364414896209553 : Int)/10^30,(-431477001747414846237624623 : Int)/10^30)
theorem v1224_mb_checked : Scalar.distance (sourceCoefficient 13 55 3 1) v1224_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1224_mg : Scalar.QComplex := ((-93086320875308079684006 : Int)/10^30,(140492300020663322595 : Int)/10^30)
theorem v1224_mg_checked : Scalar.distance (sourceCoefficient 13 55 3 2) v1224_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1224_upper : Scalar.QComplex := ((999997186280481025036155178202 : Int)/10^30,(-2372220715054228723809692241 : Int)/10^30)
theorem v1224_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 55 5) 1) 14) v1224_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1224 : Material (13 : Basis) (55 : Basis) where
  plus := ![v1224_pa,v1224_pb,v1224_pg]
  minus := ![(Primitive.Addresses.material1224 1).one,v1224_mb,v1224_mg]
  upper := v1224_upper
  lower := (Primitive.Addresses.material1224 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1224_pa_checked.trans (by decide +kernel)
    · exact v1224_pb_checked.trans (by decide +kernel)
    · exact v1224_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 55 Primitive.Addresses.material1224
    · exact v1224_mb_checked.trans (by decide +kernel)
    · exact v1224_mg_checked.trans (by decide +kernel)
  upper_error := v1224_upper_checked
  lower_error := reuse_lower_error 13 55 Primitive.Addresses.material1224

def v1225_pa : Scalar.QComplex := ((999999788779733264325657882013 : Int)/10^30,(-649954220585840648902431575 : Int)/10^30)
theorem v1225_pa_checked : Scalar.distance (sourceCoefficient 13 56 1 0) v1225_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1225_pb : Scalar.QComplex := ((-280440617565405575961493 : Int)/10^30,(-431477401712826065308277943 : Int)/10^30)
theorem v1225_pb_checked : Scalar.distance (sourceCoefficient 13 56 1 1) v1225_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1225_pg : Scalar.QComplex := ((-93086407198601256027692 : Int)/10^30,(60501916017133904808 : Int)/10^30)
theorem v1225_pg_checked : Scalar.distance (sourceCoefficient 13 56 1 2) v1225_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1225_mb : Scalar.QComplex := ((-652786077801930276331741 : Int)/10^30,(-431476999046447533803309746 : Int)/10^30)
theorem v1225_mb_checked : Scalar.distance (sourceCoefficient 13 56 3 1) v1225_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1225_mg : Scalar.QComplex := ((-93086320327848979372429 : Int)/10^30,(140831270445749444182 : Int)/10^30)
theorem v1225_mg_checked : Scalar.distance (sourceCoefficient 13 56 3 2) v1225_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1225_upper : Scalar.QComplex := ((999997177635494758929797606118 : Int)/10^30,(-2375862168717019653221452678 : Int)/10^30)
theorem v1225_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 56 5) 1) 14) v1225_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1225 : Material (13 : Basis) (56 : Basis) where
  plus := ![v1225_pa,v1225_pb,v1225_pg]
  minus := ![(Primitive.Addresses.material1225 1).one,v1225_mb,v1225_mg]
  upper := v1225_upper
  lower := (Primitive.Addresses.material1225 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1225_pa_checked.trans (by decide +kernel)
    · exact v1225_pb_checked.trans (by decide +kernel)
    · exact v1225_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 56 Primitive.Addresses.material1225
    · exact v1225_mb_checked.trans (by decide +kernel)
    · exact v1225_mg_checked.trans (by decide +kernel)
  upper_error := v1225_upper_checked
  lower_error := reuse_lower_error 13 56 Primitive.Addresses.material1225

def v1226_pa : Scalar.QComplex := ((999999781055306882160904917653 : Int)/10^30,(-661732074406930607336983450 : Int)/10^30)
theorem v1226_pa_checked : Scalar.distance (sourceCoefficient 13 57 1 0) v1226_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1226_pb : Scalar.QComplex := ((-285522495695336824656921 : Int)/10^30,(-431477397310078500233456601 : Int)/10^30)
theorem v1226_pb_checked : Scalar.distance (sourceCoefficient 13 57 1 1) v1226_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1226_pg : Scalar.QComplex := ((-93086406364159944761689 : Int)/10^30,(61598274269057323819 : Int)/10^30)
theorem v1226_pg_checked : Scalar.distance (sourceCoefficient 13 57 1 2) v1226_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1226_mb : Scalar.QComplex := ((-657867950240273187679481 : Int)/10^30,(-431476990258269661236528073 : Int)/10^30)
theorem v1226_mb_checked : Scalar.distance (sourceCoefficient 13 57 3 1) v1226_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1226_mg : Scalar.QComplex := ((-93086318547300185539815 : Int)/10^30,(141927627569363310173 : Int)/10^30)
theorem v1226_mg_checked : Scalar.distance (sourceCoefficient 13 57 3 2) v1226_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1226_upper : Scalar.QComplex := ((999997149583572664741650629570 : Int)/10^30,(-2387639991664720687910622442 : Int)/10^30)
theorem v1226_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 57 5) 1) 14) v1226_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1226 : Material (13 : Basis) (57 : Basis) where
  plus := ![v1226_pa,v1226_pb,v1226_pg]
  minus := ![(Primitive.Addresses.material1226 1).one,v1226_mb,v1226_mg]
  upper := v1226_upper
  lower := (Primitive.Addresses.material1226 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1226_pa_checked.trans (by decide +kernel)
    · exact v1226_pb_checked.trans (by decide +kernel)
    · exact v1226_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 57 Primitive.Addresses.material1226
    · exact v1226_mb_checked.trans (by decide +kernel)
    · exact v1226_mg_checked.trans (by decide +kernel)
  upper_error := v1226_upper_checked
  lower_error := reuse_lower_error 13 57 Primitive.Addresses.material1226

def v1227_pa : Scalar.QComplex := ((999999776806055220036092739765 : Int)/10^30,(-668122623284371974482612633 : Int)/10^30)
theorem v1227_pa_checked : Scalar.distance (sourceCoefficient 13 58 1 0) v1227_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1227_pb : Scalar.QComplex := ((-288279873302660848084948 : Int)/10^30,(-431477394887792395958152433 : Int)/10^30)
theorem v1227_pb_checked : Scalar.distance (sourceCoefficient 13 58 1 1) v1227_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1227_pg : Scalar.QComplex := ((-93086405905095597985414 : Int)/10^30,(62193147586560273163 : Int)/10^30)
theorem v1227_pg_checked : Scalar.distance (sourceCoefficient 13 58 1 2) v1227_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1227_mb : Scalar.QComplex := ((-660625324730575697245411 : Int)/10^30,(-431476985456491771445782845 : Int)/10^30)
theorem v1227_mb_checked : Scalar.distance (sourceCoefficient 13 58 3 1) v1227_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1227_mg : Scalar.QComplex := ((-93086317574887128788783 : Int)/10^30,(142522500269215880581 : Int)/10^30)
theorem v1227_mg_checked : Scalar.distance (sourceCoefficient 13 58 3 2) v1227_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1227_upper : Scalar.QComplex := ((999997134304819714979671076425 : Int)/10^30,(-2394030523690367308983423880 : Int)/10^30)
theorem v1227_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 58 5) 1) 14) v1227_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1227 : Material (13 : Basis) (58 : Basis) where
  plus := ![v1227_pa,v1227_pb,v1227_pg]
  minus := ![(Primitive.Addresses.material1227 1).one,v1227_mb,v1227_mg]
  upper := v1227_upper
  lower := (Primitive.Addresses.material1227 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1227_pa_checked.trans (by decide +kernel)
    · exact v1227_pb_checked.trans (by decide +kernel)
    · exact v1227_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 58 Primitive.Addresses.material1227
    · exact v1227_mb_checked.trans (by decide +kernel)
    · exact v1227_mg_checked.trans (by decide +kernel)
  upper_error := v1227_upper_checked
  lower_error := reuse_lower_error 13 58 Primitive.Addresses.material1227

def v1228_pa : Scalar.QComplex := ((999999764915581116236523746595 : Int)/10^30,(-685688546282379541534810900 : Int)/10^30)
theorem v1228_pa_checked : Scalar.distance (sourceCoefficient 13 59 1 0) v1228_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1228_pb : Scalar.QComplex := ((-295859172557732029849654 : Int)/10^30,(-431477388108521781618612530 : Int)/10^30)
theorem v1228_pb_checked : Scalar.distance (sourceCoefficient 13 59 1 1) v1228_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1228_pg : Scalar.QComplex := ((-93086404620398951310082 : Int)/10^30,(63828296467852718609 : Int)/10^30)
theorem v1228_pg_checked : Scalar.distance (sourceCoefficient 13 59 1 2) v1228_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1228_mb : Scalar.QComplex := ((-668204615313322162098268 : Int)/10^30,(-431476972136629783178698691 : Int)/10^30)
theorem v1228_mb_checked : Scalar.distance (sourceCoefficient 13 59 3 1) v1228_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1228_mg : Scalar.QComplex := ((-93086314879131120281151 : Int)/10^30,(144157647433032322034 : Int)/10^30)
theorem v1228_mg_checked : Scalar.distance (sourceCoefficient 13 59 3 2) v1228_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1228_upper : Scalar.QComplex := ((999997092097173794169574254700 : Int)/10^30,(-2411596400004116400993664016 : Int)/10^30)
theorem v1228_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 59 5) 1) 14) v1228_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1228 : Material (13 : Basis) (59 : Basis) where
  plus := ![v1228_pa,v1228_pb,v1228_pg]
  minus := ![(Primitive.Addresses.material1228 1).one,v1228_mb,v1228_mg]
  upper := v1228_upper
  lower := (Primitive.Addresses.material1228 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1228_pa_checked.trans (by decide +kernel)
    · exact v1228_pb_checked.trans (by decide +kernel)
    · exact v1228_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 59 Primitive.Addresses.material1228
    · exact v1228_mb_checked.trans (by decide +kernel)
    · exact v1228_mg_checked.trans (by decide +kernel)
  upper_error := v1228_upper_checked
  lower_error := reuse_lower_error 13 59 Primitive.Addresses.material1228

def v1229_pa : Scalar.QComplex := ((999999750815522891034376193659 : Int)/10^30,(-705952471576541486609279738 : Int)/10^30)
theorem v1229_pa_checked : Scalar.distance (sourceCoefficient 13 60 1 0) v1229_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1229_pb : Scalar.QComplex := ((-304602598790257728601292 : Int)/10^30,(-431477380067494392092700823 : Int)/10^30)
theorem v1229_pb_checked : Scalar.distance (sourceCoefficient 13 60 1 1) v1229_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1229_pg : Scalar.QComplex := ((-93086403096756227885853 : Int)/10^30,(65714592711381707599 : Int)/10^30)
theorem v1229_pg_checked : Scalar.distance (sourceCoefficient 13 60 1 2) v1229_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1229_mb : Scalar.QComplex := ((-676948031351226197430360 : Int)/10^30,(-431476956550422338324466221 : Int)/10^30)
theorem v1229_mb_checked : Scalar.distance (sourceCoefficient 13 60 3 1) v1229_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1229_mg : Scalar.QComplex := ((-93086311727700261642332 : Int)/10^30,(146043941659371963567 : Int)/10^30)
theorem v1229_mg_checked : Scalar.distance (sourceCoefficient 13 60 3 2) v1229_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1229_upper : Scalar.QComplex := ((999997043023439840566775493309 : Int)/10^30,(-2431860270782120638881824681 : Int)/10^30)
theorem v1229_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 60 5) 1) 14) v1229_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1229 : Material (13 : Basis) (60 : Basis) where
  plus := ![v1229_pa,v1229_pb,v1229_pg]
  minus := ![(Primitive.Addresses.material1229 1).one,v1229_mb,v1229_mg]
  upper := v1229_upper
  lower := (Primitive.Addresses.material1229 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1229_pa_checked.trans (by decide +kernel)
    · exact v1229_pb_checked.trans (by decide +kernel)
    · exact v1229_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 60 Primitive.Addresses.material1229
    · exact v1229_mb_checked.trans (by decide +kernel)
    · exact v1229_mg_checked.trans (by decide +kernel)
  upper_error := v1229_upper_checked
  lower_error := reuse_lower_error 13 60 Primitive.Addresses.material1229

def v1230_pa : Scalar.QComplex := ((999999746661944549688706292558 : Int)/10^30,(-711811805690557683707573902 : Int)/10^30)
theorem v1230_pa_checked : Scalar.distance (sourceCoefficient 13 61 1 0) v1230_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1230_pb : Scalar.QComplex := ((-307130769142032381707677 : Int)/10^30,(-431477377698393945280381600 : Int)/10^30)
theorem v1230_pb_checked : Scalar.distance (sourceCoefficient 13 61 1 1) v1230_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1230_pg : Scalar.QComplex := ((-93086402647881929103973 : Int)/10^30,(66260017140211042385 : Int)/10^30)
theorem v1230_pg_checked : Scalar.distance (sourceCoefficient 13 61 1 2) v1230_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1230_mb : Scalar.QComplex := ((-679476198717220500202212 : Int)/10^30,(-431476951999625624620783518 : Int)/10^30)
theorem v1230_mb_checked : Scalar.distance (sourceCoefficient 13 61 3 1) v1230_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1230_mg : Scalar.QComplex := ((-93086310808149412921531 : Int)/10^30,(146589365497756553071 : Int)/10^30)
theorem v1230_mg_checked : Scalar.distance (sourceCoefficient 13 61 3 2) v1230_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1230_upper : Scalar.QComplex := ((999997028757188559334721832248 : Int)/10^30,(-2437719589000647551408486320 : Int)/10^30)
theorem v1230_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 61 5) 1) 14) v1230_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1230 : Material (13 : Basis) (61 : Basis) where
  plus := ![v1230_pa,v1230_pb,v1230_pg]
  minus := ![(Primitive.Addresses.material1230 1).one,v1230_mb,v1230_mg]
  upper := v1230_upper
  lower := (Primitive.Addresses.material1230 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1230_pa_checked.trans (by decide +kernel)
    · exact v1230_pb_checked.trans (by decide +kernel)
    · exact v1230_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 61 Primitive.Addresses.material1230
    · exact v1230_mb_checked.trans (by decide +kernel)
    · exact v1230_mg_checked.trans (by decide +kernel)
  upper_error := v1230_upper_checked
  lower_error := reuse_lower_error 13 61 Primitive.Addresses.material1230

def v1231_pa : Scalar.QComplex := ((999999740565793419651038323075 : Int)/10^30,(-720325166750815655116890636 : Int)/10^30)
theorem v1231_pa_checked : Scalar.distance (sourceCoefficient 13 62 1 0) v1231_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1231_pb : Scalar.QComplex := ((-310804092168155789488095 : Int)/10^30,(-431477374220995589265715765 : Int)/10^30)
theorem v1231_pb_checked : Scalar.distance (sourceCoefficient 13 62 1 1) v1231_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1231_pg : Scalar.QComplex := ((-93086401989042633088271 : Int)/10^30,(67052495430701544049 : Int)/10^30)
theorem v1231_pg_checked : Scalar.distance (sourceCoefficient 13 62 1 2) v1231_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1231_mb : Scalar.QComplex := ((-683149517374759701168624 : Int)/10^30,(-431476945352316232183612624 : Int)/10^30)
theorem v1231_mb_checked : Scalar.distance (sourceCoefficient 13 62 3 1) v1231_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1231_mg : Scalar.QComplex := ((-93086309465437289425764 : Int)/10^30,(147381842924622529697 : Int)/10^30)
theorem v1231_mg_checked : Scalar.distance (sourceCoefficient 13 62 3 2) v1231_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1231_upper : Scalar.QComplex := ((999997007967757644875105520007 : Int)/10^30,(-2446232926859850461268750555 : Int)/10^30)
theorem v1231_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 62 5) 1) 14) v1231_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1231 : Material (13 : Basis) (62 : Basis) where
  plus := ![v1231_pa,v1231_pb,v1231_pg]
  minus := ![(Primitive.Addresses.material1231 1).one,v1231_mb,v1231_mg]
  upper := v1231_upper
  lower := (Primitive.Addresses.material1231 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1231_pa_checked.trans (by decide +kernel)
    · exact v1231_pb_checked.trans (by decide +kernel)
    · exact v1231_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 62 Primitive.Addresses.material1231
    · exact v1231_mb_checked.trans (by decide +kernel)
    · exact v1231_mg_checked.trans (by decide +kernel)
  upper_error := v1231_upper_checked
  lower_error := reuse_lower_error 13 62 Primitive.Addresses.material1231

def v1232_pa : Scalar.QComplex := ((999999722397805457031879448899 : Int)/10^30,(-745120333921278668274864778 : Int)/10^30)
theorem v1232_pa_checked : Scalar.distance (sourceCoefficient 13 63 1 0) v1232_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1232_pb : Scalar.QComplex := ((-321502646685325510751547 : Int)/10^30,(-431477363855502716994199277 : Int)/10^30)
theorem v1232_pb_checked : Scalar.distance (sourceCoefficient 13 63 1 1) v1232_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1232_pg : Scalar.QComplex := ((-93086400025326717978542 : Int)/10^30,(69360588725052812051 : Int)/10^30)
theorem v1232_pg_checked : Scalar.distance (sourceCoefficient 13 63 1 2) v1232_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1232_mb : Scalar.QComplex := ((-693848058963415123292395 : Int)/10^30,(-431476925754456516149875284 : Int)/10^30)
theorem v1232_mb_checked : Scalar.distance (sourceCoefficient 13 63 3 1) v1232_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1232_mg : Scalar.QComplex := ((-93086305509941545135146 : Int)/10^30,(149689933664966786879 : Int)/10^30)
theorem v1232_mg_checked : Scalar.distance (sourceCoefficient 13 63 3 2) v1232_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1232_upper : Scalar.QComplex := ((999996947005587605115050409608 : Int)/10^30,(-2471028025744525582472427132 : Int)/10^30)
theorem v1232_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 63 5) 1) 14) v1232_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1232 : Material (13 : Basis) (63 : Basis) where
  plus := ![v1232_pa,v1232_pb,v1232_pg]
  minus := ![(Primitive.Addresses.material1232 1).one,v1232_mb,v1232_mg]
  upper := v1232_upper
  lower := (Primitive.Addresses.material1232 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1232_pa_checked.trans (by decide +kernel)
    · exact v1232_pb_checked.trans (by decide +kernel)
    · exact v1232_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 63 Primitive.Addresses.material1232
    · exact v1232_mb_checked.trans (by decide +kernel)
    · exact v1232_mg_checked.trans (by decide +kernel)
  upper_error := v1232_upper_checked
  lower_error := reuse_lower_error 13 63 Primitive.Addresses.material1232

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
