import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B054

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1297_pa : Scalar.QComplex := ((999999857496925723729842986555 : Int)/10^30,(-533859652198416410573158643 : Int)/10^30)
theorem v1297_pa_checked : Scalar.distance (sourceCoefficient 14 45 1 0) v1297_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1297_pb : Scalar.QComplex := ((-230348430559427061112935 : Int)/10^30,(-431477443154770097078975707 : Int)/10^30)
theorem v1297_pb_checked : Scalar.distance (sourceCoefficient 14 45 1 1) v1297_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1297_pg : Scalar.QComplex := ((-93086414867237343735352 : Int)/10^30,(49695088147123664234 : Int)/10^30)
theorem v1297_pg_checked : Scalar.distance (sourceCoefficient 14 45 1 2) v1297_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1297_mb : Scalar.QComplex := ((-602693945210093533395920 : Int)/10^30,(-431477083715677452650157066 : Int)/10^30)
theorem v1297_mb_checked : Scalar.distance (sourceCoefficient 14 45 3 1) v1297_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1297_mg : Scalar.QComplex := ((-93086337322287942055922 : Int)/10^30,(130024453217302677189 : Int)/10^30)
theorem v1297_mg_checked : Scalar.distance (sourceCoefficient 14 45 3 2) v1297_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1297_upper : Scalar.QComplex := ((999997446721277891869632773191 : Int)/10^30,(-2259767891838457811909716940 : Int)/10^30)
theorem v1297_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 45 5) 1) 14) v1297_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1297 : Material (14 : Basis) (45 : Basis) where
  plus := ![v1297_pa,v1297_pb,v1297_pg]
  minus := ![(Primitive.Addresses.material1297 1).one,v1297_mb,v1297_mg]
  upper := v1297_upper
  lower := (Primitive.Addresses.material1297 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1297_pa_checked.trans (by decide +kernel)
    · exact v1297_pb_checked.trans (by decide +kernel)
    · exact v1297_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 45 Primitive.Addresses.material1297
    · exact v1297_mb_checked.trans (by decide +kernel)
    · exact v1297_mg_checked.trans (by decide +kernel)
  upper_error := v1297_upper_checked
  lower_error := reuse_lower_error 14 45 Primitive.Addresses.material1297

def v1298_pa : Scalar.QComplex := ((999999848626822311994997859696 : Int)/10^30,(-550223893030983416341130455 : Int)/10^30)
theorem v1298_pa_checked : Scalar.distance (sourceCoefficient 14 46 1 0) v1298_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1298_pb : Scalar.QComplex := ((-237409231730965030486011 : Int)/10^30,(-431477438185707005989239237 : Int)/10^30)
theorem v1298_pb_checked : Scalar.distance (sourceCoefficient 14 46 1 1) v1298_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1298_pg : Scalar.QComplex := ((-93086413918384433200206 : Int)/10^30,(51218376807555455605 : Int)/10^30)
theorem v1298_pg_checked : Scalar.distance (sourceCoefficient 14 46 1 2) v1298_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1298_mb : Scalar.QComplex := ((-609754739464494882733833 : Int)/10^30,(-431477072653462807412242461 : Int)/10^30)
theorem v1298_mb_checked : Scalar.distance (sourceCoefficient 14 46 3 1) v1298_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1298_mg : Scalar.QComplex := ((-93086335058905877243921 : Int)/10^30,(131547740491727155508 : Int)/10^30)
theorem v1298_mg_checked : Scalar.distance (sourceCoefficient 14 46 3 2) v1298_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1298_upper : Scalar.QComplex := ((999997409607992566432856001190 : Int)/10^30,(-2276132092989416577171325566 : Int)/10^30)
theorem v1298_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 46 5) 1) 14) v1298_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1298 : Material (14 : Basis) (46 : Basis) where
  plus := ![v1298_pa,v1298_pb,v1298_pg]
  minus := ![(Primitive.Addresses.material1298 1).one,v1298_mb,v1298_mg]
  upper := v1298_upper
  lower := (Primitive.Addresses.material1298 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1298_pa_checked.trans (by decide +kernel)
    · exact v1298_pb_checked.trans (by decide +kernel)
    · exact v1298_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 46 Primitive.Addresses.material1298
    · exact v1298_mb_checked.trans (by decide +kernel)
    · exact v1298_mg_checked.trans (by decide +kernel)
  upper_error := v1298_upper_checked
  lower_error := reuse_lower_error 14 46 Primitive.Addresses.material1298

def v1299_pa : Scalar.QComplex := ((999999846452263035756028488743 : Int)/10^30,(-554161935134108986720528927 : Int)/10^30)
theorem v1299_pa_checked : Scalar.distance (sourceCoefficient 14 47 1 0) v1299_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1299_pb : Scalar.QComplex := ((-239108408150842030515301 : Int)/10^30,(-431477436966907638588197989 : Int)/10^30)
theorem v1299_pb_checked : Scalar.distance (sourceCoefficient 14 47 1 1) v1299_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1299_pg : Scalar.QComplex := ((-93086413685702314892299 : Int)/10^30,(51584955063516112677 : Int)/10^30)
theorem v1299_pg_checked : Scalar.distance (sourceCoefficient 14 47 1 2) v1299_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1299_mb : Scalar.QComplex := ((-611453914199921884062931 : Int)/10^30,(-431477069968351171537152501 : Int)/10^30)
theorem v1299_mb_checked : Scalar.distance (sourceCoefficient 14 47 3 1) v1299_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1299_mg : Scalar.QComplex := ((-93086334509883320751919 : Int)/10^30,(131914318410399785945 : Int)/10^30)
theorem v1299_mg_checked : Scalar.distance (sourceCoefficient 14 47 3 2) v1299_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1299_upper : Scalar.QComplex := ((999997400636733115338614229889 : Int)/10^30,(-2280070125474198993554196554 : Int)/10^30)
theorem v1299_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 47 5) 1) 14) v1299_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1299 : Material (14 : Basis) (47 : Basis) where
  plus := ![v1299_pa,v1299_pb,v1299_pg]
  minus := ![(Primitive.Addresses.material1299 1).one,v1299_mb,v1299_mg]
  upper := v1299_upper
  lower := (Primitive.Addresses.material1299 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1299_pa_checked.trans (by decide +kernel)
    · exact v1299_pb_checked.trans (by decide +kernel)
    · exact v1299_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 47 Primitive.Addresses.material1299
    · exact v1299_mb_checked.trans (by decide +kernel)
    · exact v1299_mg_checked.trans (by decide +kernel)
  upper_error := v1299_upper_checked
  lower_error := reuse_lower_error 14 47 Primitive.Addresses.material1299

def v1300_pa : Scalar.QComplex := ((999999830875068523181729548024 : Int)/10^30,(-581592498533461222174237934 : Int)/10^30)
theorem v1300_pa_checked : Scalar.distance (sourceCoefficient 14 48 1 0) v1300_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1300_pb : Scalar.QComplex := ((-250944077985866020892598 : Int)/10^30,(-431477428229807652738320456 : Int)/10^30)
theorem v1300_pb_checked : Scalar.distance (sourceCoefficient 14 48 1 1) v1300_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1300_pg : Scalar.QComplex := ((-93086412018223998006763 : Int)/10^30,(54138368101341903054 : Int)/10^30)
theorem v1300_pg_checked : Scalar.distance (sourceCoefficient 14 48 1 2) v1300_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1300_mb : Scalar.QComplex := ((-623289572088261294614851 : Int)/10^30,(-431477051017604430064498573 : Int)/10^30)
theorem v1300_mb_checked : Scalar.distance (sourceCoefficient 14 48 3 1) v1300_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1300_mg : Scalar.QComplex := ((-93086330638925174555280 : Int)/10^30,(134467729058514518561 : Int)/10^30)
theorem v1300_mg_checked : Scalar.distance (sourceCoefficient 14 48 3 2) v1300_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1300_upper : Scalar.QComplex := ((999997337716897857156397880966 : Int)/10^30,(-2307500621134124689342274018 : Int)/10^30)
theorem v1300_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 48 5) 1) 14) v1300_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1300 : Material (14 : Basis) (48 : Basis) where
  plus := ![v1300_pa,v1300_pb,v1300_pg]
  minus := ![(Primitive.Addresses.material1300 1).one,v1300_mb,v1300_mg]
  upper := v1300_upper
  lower := (Primitive.Addresses.material1300 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1300_pa_checked.trans (by decide +kernel)
    · exact v1300_pb_checked.trans (by decide +kernel)
    · exact v1300_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 48 Primitive.Addresses.material1300
    · exact v1300_mb_checked.trans (by decide +kernel)
    · exact v1300_mg_checked.trans (by decide +kernel)
  upper_error := v1300_upper_checked
  lower_error := reuse_lower_error 14 48 Primitive.Addresses.material1300

def v1301_pa : Scalar.QComplex := ((999999817814864526852289608904 : Int)/10^30,(-603630878728773975079764078 : Int)/10^30)
theorem v1301_pa_checked : Scalar.distance (sourceCoefficient 14 49 1 0) v1301_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1301_pb : Scalar.QComplex := ((-260453142178135029518326 : Int)/10^30,(-431477420896607151703410356 : Int)/10^30)
theorem v1301_pb_checked : Scalar.distance (sourceCoefficient 14 49 1 1) v1301_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1301_pg : Scalar.QComplex := ((-93086410619332285972824 : Int)/10^30,(56189842076809016027 : Int)/10^30)
theorem v1301_pg_checked : Scalar.distance (sourceCoefficient 14 49 1 2) v1301_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1301_mb : Scalar.QComplex := ((-632798626411649361453323 : Int)/10^30,(-431477035478512533940127134 : Int)/10^30)
theorem v1301_mb_checked : Scalar.distance (sourceCoefficient 14 49 3 1) v1301_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1301_mg : Scalar.QComplex := ((-93086327469704337522532 : Int)/10^30,(136519201062943569734 : Int)/10^30)
theorem v1301_mg_checked : Scalar.distance (sourceCoefficient 14 49 3 2) v1301_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1301_upper : Scalar.QComplex := ((999997286620468401590435181005 : Int)/10^30,(-2329538945965131666107866193 : Int)/10^30)
theorem v1301_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 49 5) 1) 14) v1301_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1301 : Material (14 : Basis) (49 : Basis) where
  plus := ![v1301_pa,v1301_pb,v1301_pg]
  minus := ![(Primitive.Addresses.material1301 1).one,v1301_mb,v1301_mg]
  upper := v1301_upper
  lower := (Primitive.Addresses.material1301 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1301_pa_checked.trans (by decide +kernel)
    · exact v1301_pb_checked.trans (by decide +kernel)
    · exact v1301_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 49 Primitive.Addresses.material1301
    · exact v1301_mb_checked.trans (by decide +kernel)
    · exact v1301_mg_checked.trans (by decide +kernel)
  upper_error := v1301_upper_checked
  lower_error := reuse_lower_error 14 49 Primitive.Addresses.material1301

def v1302_pa : Scalar.QComplex := ((999999816257029297580260097863 : Int)/10^30,(-606206159357821270606686993 : Int)/10^30)
theorem v1302_pa_checked : Scalar.distance (sourceCoefficient 14 50 1 0) v1302_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1302_pb : Scalar.QComplex := ((-261564317701433923513665 : Int)/10^30,(-431477420021457354791589399 : Int)/10^30)
theorem v1302_pb_checked : Scalar.distance (sourceCoefficient 14 50 1 1) v1302_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1302_pg : Scalar.QComplex := ((-93086410452423755414418 : Int)/10^30,(56429565737305598694 : Int)/10^30)
theorem v1302_pg_checked : Scalar.distance (sourceCoefficient 14 50 1 2) v1302_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1302_mb : Scalar.QComplex := ((-633909800765991965443114 : Int)/10^30,(-431477033644468631767419920 : Int)/10^30)
theorem v1302_mb_checked : Scalar.distance (sourceCoefficient 14 50 3 1) v1302_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1302_mg : Scalar.QComplex := ((-93086327095925146856124 : Int)/10^30,(136758924490145533096 : Int)/10^30)
theorem v1302_mg_checked : Scalar.distance (sourceCoefficient 14 50 3 2) v1302_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1302_upper : Scalar.QComplex := ((999997280617934754429019659810 : Int)/10^30,(-2332114220069918698366460408 : Int)/10^30)
theorem v1302_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 50 5) 1) 14) v1302_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1302 : Material (14 : Basis) (50 : Basis) where
  plus := ![v1302_pa,v1302_pb,v1302_pg]
  minus := ![(Primitive.Addresses.material1302 1).one,v1302_mb,v1302_mg]
  upper := v1302_upper
  lower := (Primitive.Addresses.material1302 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1302_pa_checked.trans (by decide +kernel)
    · exact v1302_pb_checked.trans (by decide +kernel)
    · exact v1302_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 50 Primitive.Addresses.material1302
    · exact v1302_mb_checked.trans (by decide +kernel)
    · exact v1302_mg_checked.trans (by decide +kernel)
  upper_error := v1302_upper_checked
  lower_error := reuse_lower_error 14 50 Primitive.Addresses.material1302

def v1303_pa : Scalar.QComplex := ((999999809343517522364136909301 : Int)/10^30,(-617505407753954342190788972 : Int)/10^30)
theorem v1303_pa_checked : Scalar.distance (sourceCoefficient 14 51 1 0) v1303_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1303_pb : Scalar.QComplex := ((-266439688586490602247331 : Int)/10^30,(-431477416136572408113179283 : Int)/10^30)
theorem v1303_pb_checked : Scalar.distance (sourceCoefficient 14 51 1 1) v1303_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1303_pg : Scalar.QComplex := ((-93086409711586539672637 : Int)/10^30,(57481372344501160787 : Int)/10^30)
theorem v1303_pg_checked : Scalar.distance (sourceCoefficient 14 51 1 2) v1303_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1303_mb : Scalar.QComplex := ((-638785166483244507952811 : Int)/10^30,(-431477025552359636358833618 : Int)/10^30)
theorem v1303_mb_checked : Scalar.distance (sourceCoefficient 14 51 3 1) v1303_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1303_mg : Scalar.QComplex := ((-93086325447426476563197 : Int)/10^30,(137810730066396274278 : Int)/10^30)
theorem v1303_mg_checked : Scalar.distance (sourceCoefficient 14 51 3 2) v1303_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1303_upper : Scalar.QComplex := ((999997254202955604158055368112 : Int)/10^30,(-2343413439705054451730797525 : Int)/10^30)
theorem v1303_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 51 5) 1) 14) v1303_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1303 : Material (14 : Basis) (51 : Basis) where
  plus := ![v1303_pa,v1303_pb,v1303_pg]
  minus := ![(Primitive.Addresses.material1303 1).one,v1303_mb,v1303_mg]
  upper := v1303_upper
  lower := (Primitive.Addresses.material1303 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1303_pa_checked.trans (by decide +kernel)
    · exact v1303_pb_checked.trans (by decide +kernel)
    · exact v1303_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 51 Primitive.Addresses.material1303
    · exact v1303_mb_checked.trans (by decide +kernel)
    · exact v1303_mg_checked.trans (by decide +kernel)
  upper_error := v1303_upper_checked
  lower_error := reuse_lower_error 14 51 Primitive.Addresses.material1303

def v1304_pa : Scalar.QComplex := ((999999794114168974206300327797 : Int)/10^30,(-641694335071311021592270535 : Int)/10^30)
theorem v1304_pa_checked : Scalar.distance (sourceCoefficient 14 52 1 0) v1304_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1304_pb : Scalar.QComplex := ((-276876665155868539551505 : Int)/10^30,(-431477407573057579754187861 : Int)/10^30)
theorem v1304_pb_checked : Scalar.distance (sourceCoefficient 14 52 1 1) v1304_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1304_pg : Scalar.QComplex := ((-93086408079022616028178 : Int)/10^30,(59733033034630277925 : Int)/10^30)
theorem v1304_pg_checked : Scalar.distance (sourceCoefficient 14 52 1 2) v1304_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1304_mb : Scalar.QComplex := ((-649222131776531464601114 : Int)/10^30,(-431477007982207281189714664 : Int)/10^30)
theorem v1304_mb_checked : Scalar.distance (sourceCoefficient 14 52 3 1) v1304_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1304_mg : Scalar.QComplex := ((-93086321871781396248400 : Int)/10^30,(140062388509300072347 : Int)/10^30)
theorem v1304_mg_checked : Scalar.distance (sourceCoefficient 14 52 3 2) v1304_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1304_upper : Scalar.QComplex := ((999997197225735590912787865655 : Int)/10^30,(-2367602304711371324519272829 : Int)/10^30)
theorem v1304_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 52 5) 1) 14) v1304_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1304 : Material (14 : Basis) (52 : Basis) where
  plus := ![v1304_pa,v1304_pb,v1304_pg]
  minus := ![(Primitive.Addresses.material1304 1).one,v1304_mb,v1304_mg]
  upper := v1304_upper
  lower := (Primitive.Addresses.material1304 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1304_pa_checked.trans (by decide +kernel)
    · exact v1304_pb_checked.trans (by decide +kernel)
    · exact v1304_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 52 Primitive.Addresses.material1304
    · exact v1304_mb_checked.trans (by decide +kernel)
    · exact v1304_mg_checked.trans (by decide +kernel)
  upper_error := v1304_upper_checked
  lower_error := reuse_lower_error 14 52 Primitive.Addresses.material1304

def v1305_pa : Scalar.QComplex := ((999999791731318900369618677957 : Int)/10^30,(-645397024182337887284169616 : Int)/10^30)
theorem v1305_pa_checked : Scalar.distance (sourceCoefficient 14 53 1 0) v1305_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1305_pb : Scalar.QComplex := ((-278474291981843745386952 : Int)/10^30,(-431477406232501554751035868 : Int)/10^30)
theorem v1305_pb_checked : Scalar.distance (sourceCoefficient 14 53 1 1) v1305_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1305_pg : Scalar.QComplex := ((-93086407823512158440594 : Int)/10^30,(60077703113422234150 : Int)/10^30)
theorem v1305_pg_checked : Scalar.distance (sourceCoefficient 14 53 1 2) v1305_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1305_mb : Scalar.QComplex := ((-650819756850797714797392 : Int)/10^30,(-431477005262971758961402092 : Int)/10^30)
theorem v1305_mb_checked : Scalar.distance (sourceCoefficient 14 53 3 1) v1305_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1305_mg : Scalar.QComplex := ((-93086321318836279165673 : Int)/10^30,(140407058239261588904 : Int)/10^30)
theorem v1305_mg_checked : Scalar.distance (sourceCoefficient 14 53 3 2) v1305_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1305_upper : Scalar.QComplex := ((999997188452383565751215679260 : Int)/10^30,(-2371304984195094650781051395 : Int)/10^30)
theorem v1305_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 53 5) 1) 14) v1305_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1305 : Material (14 : Basis) (53 : Basis) where
  plus := ![v1305_pa,v1305_pb,v1305_pg]
  minus := ![(Primitive.Addresses.material1305 1).one,v1305_mb,v1305_mg]
  upper := v1305_upper
  lower := (Primitive.Addresses.material1305 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1305_pa_checked.trans (by decide +kernel)
    · exact v1305_pb_checked.trans (by decide +kernel)
    · exact v1305_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 53 Primitive.Addresses.material1305
    · exact v1305_mb_checked.trans (by decide +kernel)
    · exact v1305_mg_checked.trans (by decide +kernel)
  upper_error := v1305_upper_checked
  lower_error := reuse_lower_error 14 53 Primitive.Addresses.material1305

def v1306_pa : Scalar.QComplex := ((999999790514606516884941349382 : Int)/10^30,(-647279493790819882270157790 : Int)/10^30)
theorem v1306_pa_checked : Scalar.distance (sourceCoefficient 14 54 1 0) v1306_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1306_pb : Scalar.QComplex := ((-279286535151690397545196 : Int)/10^30,(-431477405547930398746372663 : Int)/10^30)
theorem v1306_pb_checked : Scalar.distance (sourceCoefficient 14 54 1 1) v1306_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1306_pg : Scalar.QComplex := ((-93086407693038182634152 : Int)/10^30,(60252935472465532420 : Int)/10^30)
theorem v1306_pg_checked : Scalar.distance (sourceCoefficient 14 54 1 2) v1306_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1306_mb : Scalar.QComplex := ((-651631999127455037783340 : Int)/10^30,(-431477003877471584350585362 : Int)/10^30)
theorem v1306_mb_checked : Scalar.distance (sourceCoefficient 14 54 3 1) v1306_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1306_mg : Scalar.QComplex := ((-93086321037144718258769 : Int)/10^30,(140582290420464706596 : Int)/10^30)
theorem v1306_mg_checked : Scalar.distance (sourceCoefficient 14 54 3 2) v1306_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1306_upper : Scalar.QComplex := ((999997183986701226485635300133 : Int)/10^30,(-2373187448899924099737525680 : Int)/10^30)
theorem v1306_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 54 5) 1) 14) v1306_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1306 : Material (14 : Basis) (54 : Basis) where
  plus := ![v1306_pa,v1306_pb,v1306_pg]
  minus := ![(Primitive.Addresses.material1306 1).one,v1306_mb,v1306_mg]
  upper := v1306_upper
  lower := (Primitive.Addresses.material1306 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1306_pa_checked.trans (by decide +kernel)
    · exact v1306_pb_checked.trans (by decide +kernel)
    · exact v1306_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 54 Primitive.Addresses.material1306
    · exact v1306_mb_checked.trans (by decide +kernel)
    · exact v1306_mg_checked.trans (by decide +kernel)
  upper_error := v1306_upper_checked
  lower_error := reuse_lower_error 14 54 Primitive.Addresses.material1306

def v1307_pa : Scalar.QComplex := ((999999780465298500994065510657 : Int)/10^30,(-662623086529987050919142022 : Int)/10^30)
theorem v1307_pa_checked : Scalar.distance (sourceCoefficient 14 55 1 0) v1307_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1307_pb : Scalar.QComplex := ((-285906949250942451149103 : Int)/10^30,(-431477399892113412035470384 : Int)/10^30)
theorem v1307_pb_checked : Scalar.distance (sourceCoefficient 14 55 1 1) v1307_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1307_pg : Scalar.QComplex := ((-93086406615221577634294 : Int)/10^30,(61681215606530782744 : Int)/10^30)
theorem v1307_pg_checked : Scalar.distance (sourceCoefficient 14 55 1 2) v1307_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1307_mb : Scalar.QComplex := ((-658252405880909023373820 : Int)/10^30,(-431476992508537508286659772 : Int)/10^30)
theorem v1307_mb_checked : Scalar.distance (sourceCoefficient 14 55 3 1) v1307_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1307_mg : Scalar.QComplex := ((-93086318726787086230275 : Int)/10^30,(142010569092608800324 : Int)/10^30)
theorem v1307_mg_checked : Scalar.distance (sourceCoefficient 14 55 3 2) v1307_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1307_upper : Scalar.QComplex := ((999997147455759069915944933680 : Int)/10^30,(-2388531001442418299084801625 : Int)/10^30)
theorem v1307_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 55 5) 1) 14) v1307_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1307 : Material (14 : Basis) (55 : Basis) where
  plus := ![v1307_pa,v1307_pb,v1307_pg]
  minus := ![(Primitive.Addresses.material1307 1).one,v1307_mb,v1307_mg]
  upper := v1307_upper
  lower := (Primitive.Addresses.material1307 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1307_pa_checked.trans (by decide +kernel)
    · exact v1307_pb_checked.trans (by decide +kernel)
    · exact v1307_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 55 Primitive.Addresses.material1307
    · exact v1307_mb_checked.trans (by decide +kernel)
    · exact v1307_mg_checked.trans (by decide +kernel)
  upper_error := v1307_upper_checked
  lower_error := reuse_lower_error 14 55 Primitive.Addresses.material1307

def v1308_pa : Scalar.QComplex := ((999999778045750307501655726776 : Int)/10^30,(-666264549650743260964857027 : Int)/10^30)
theorem v1308_pa_checked : Scalar.distance (sourceCoefficient 14 56 1 0) v1308_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1308_pb : Scalar.QComplex := ((-287478158423026185497925 : Int)/10^30,(-431477398529943727175504553 : Int)/10^30)
theorem v1308_pb_checked : Scalar.distance (sourceCoefficient 14 56 1 1) v1308_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1308_pg : Scalar.QComplex := ((-93086406355671619343263 : Int)/10^30,(62020186374811569287 : Int)/10^30)
theorem v1308_pg_checked : Scalar.distance (sourceCoefficient 14 56 1 2) v1308_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1308_mb : Scalar.QComplex := ((-659823613292468686960369 : Int)/10^30,(-431476989790485579750663052 : Int)/10^30)
theorem v1308_mb_checked : Scalar.distance (sourceCoefficient 14 56 3 1) v1308_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1308_mg : Scalar.QComplex := ((-93086318174720718231914 : Int)/10^30,(142349539510695353798 : Int)/10^30)
theorem v1308_mg_checked : Scalar.distance (sourceCoefficient 14 56 3 2) v1308_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1308_upper : Scalar.QComplex := ((999997138751379484584885691284 : Int)/10^30,(-2392172454963722264800124246 : Int)/10^30)
theorem v1308_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 56 5) 1) 14) v1308_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1308 : Material (14 : Basis) (56 : Basis) where
  plus := ![v1308_pa,v1308_pb,v1308_pg]
  minus := ![(Primitive.Addresses.material1308 1).one,v1308_mb,v1308_mg]
  upper := v1308_upper
  lower := (Primitive.Addresses.material1308 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1308_pa_checked.trans (by decide +kernel)
    · exact v1308_pb_checked.trans (by decide +kernel)
    · exact v1308_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 56 Primitive.Addresses.material1308
    · exact v1308_mb_checked.trans (by decide +kernel)
    · exact v1308_mg_checked.trans (by decide +kernel)
  upper_error := v1308_upper_checked
  lower_error := reuse_lower_error 14 56 Primitive.Addresses.material1308

def v1309_pa : Scalar.QComplex := ((999999770129223213270266956408 : Int)/10^30,(-678042403344278642728286098 : Int)/10^30)
theorem v1309_pa_checked : Scalar.distance (sourceCoefficient 14 57 1 0) v1309_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1309_pb : Scalar.QComplex := ((-292560036516266147490804 : Int)/10^30,(-431477394071938071907965120 : Int)/10^30)
theorem v1309_pb_checked : Scalar.distance (sourceCoefficient 14 57 1 1) v1309_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1309_pg : Scalar.QComplex := ((-93086405506328667211551 : Int)/10^30,(63116544616840321735 : Int)/10^30)
theorem v1309_pg_checked : Scalar.distance (sourceCoefficient 14 57 1 2) v1309_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1309_mb : Scalar.QComplex := ((-664905485646435082163083 : Int)/10^30,(-431476980947049669229203597 : Int)/10^30)
theorem v1309_mb_checked : Scalar.distance (sourceCoefficient 14 57 3 1) v1309_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1309_mg : Scalar.QComplex := ((-93086316379270297620806 : Int)/10^30,(143445896611555111988 : Int)/10^30)
theorem v1309_mg_checked : Scalar.distance (sourceCoefficient 14 57 3 2) v1309_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1309_upper : Scalar.QComplex := ((999997110507357184589175470742 : Int)/10^30,(-2403950277452320511009180696 : Int)/10^30)
theorem v1309_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 57 5) 1) 14) v1309_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1309 : Material (14 : Basis) (57 : Basis) where
  plus := ![v1309_pa,v1309_pb,v1309_pg]
  minus := ![(Primitive.Addresses.material1309 1).one,v1309_mb,v1309_mg]
  upper := v1309_upper
  lower := (Primitive.Addresses.material1309 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1309_pa_checked.trans (by decide +kernel)
    · exact v1309_pb_checked.trans (by decide +kernel)
    · exact v1309_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 57 Primitive.Addresses.material1309
    · exact v1309_mb_checked.trans (by decide +kernel)
    · exact v1309_mg_checked.trans (by decide +kernel)
  upper_error := v1309_upper_checked
  lower_error := reuse_lower_error 14 57 Primitive.Addresses.material1309

def v1310_pa : Scalar.QComplex := ((999999765775739574045863682622 : Int)/10^30,(-684432952151563272867230047 : Int)/10^30)
theorem v1310_pa_checked : Scalar.distance (sourceCoefficient 14 58 1 0) v1310_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1310_pb : Scalar.QComplex := ((-295317414103409468541259 : Int)/10^30,(-431477391619669465626264025 : Int)/10^30)
theorem v1310_pb_checked : Scalar.distance (sourceCoefficient 14 58 1 1) v1310_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1310_pg : Scalar.QComplex := ((-93086405039178835109957 : Int)/10^30,(63711417928901071063 : Int)/10^30)
theorem v1310_pg_checked : Scalar.distance (sourceCoefficient 14 58 1 2) v1310_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1310_mb : Scalar.QComplex := ((-667662860090683347995882 : Int)/10^30,(-431476976115289306010954454 : Int)/10^30)
theorem v1310_mb_checked : Scalar.distance (sourceCoefficient 14 58 3 1) v1310_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1310_mg : Scalar.QComplex := ((-93086315398771763251423 : Int)/10^30,(144040769298988074726 : Int)/10^30)
theorem v1310_mg_checked : Scalar.distance (sourceCoefficient 14 58 3 2) v1310_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1310_upper : Scalar.QComplex := ((999997095124372534053054267494 : Int)/10^30,(-2410340809227915562942718671 : Int)/10^30)
theorem v1310_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 58 5) 1) 14) v1310_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1310 : Material (14 : Basis) (58 : Basis) where
  plus := ![v1310_pa,v1310_pb,v1310_pg]
  minus := ![(Primitive.Addresses.material1310 1).one,v1310_mb,v1310_mg]
  upper := v1310_upper
  lower := (Primitive.Addresses.material1310 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1310_pa_checked.trans (by decide +kernel)
    · exact v1310_pb_checked.trans (by decide +kernel)
    · exact v1310_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 58 Primitive.Addresses.material1310
    · exact v1310_mb_checked.trans (by decide +kernel)
    · exact v1310_mg_checked.trans (by decide +kernel)
  upper_error := v1310_upper_checked
  lower_error := reuse_lower_error 14 58 Primitive.Addresses.material1310

def v1311_pa : Scalar.QComplex := ((999999753598759425367139430567 : Int)/10^30,(-701998874953296748102755572 : Int)/10^30)
theorem v1311_pa_checked : Scalar.distance (sourceCoefficient 14 59 1 0) v1311_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1311_pb : Scalar.QComplex := ((-302896713302022080619083 : Int)/10^30,(-431477384757984909890715893 : Int)/10^30)
theorem v1311_pb_checked : Scalar.distance (sourceCoefficient 14 59 1 1) v1311_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1311_pg : Scalar.QComplex := ((-93086403732257334950905 : Int)/10^30,(65346566794968138158 : Int)/10^30)
theorem v1311_pg_checked : Scalar.distance (sourceCoefficient 14 59 1 2) v1311_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1311_mb : Scalar.QComplex := ((-675242150545851744545339 : Int)/10^30,(-431476962713013455755541796 : Int)/10^30)
theorem v1311_mb_checked : Scalar.distance (sourceCoefficient 14 59 3 1) v1311_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1311_mg : Scalar.QComplex := ((-93086312680790922674215 : Int)/10^30,(145675916428400095911 : Int)/10^30)
theorem v1311_mg_checked : Scalar.distance (sourceCoefficient 14 59 3 2) v1311_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1311_upper : Scalar.QComplex := ((999997052630221333832177299253 : Int)/10^30,(-2427906684850907413627423877 : Int)/10^30)
theorem v1311_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 59 5) 1) 14) v1311_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1311 : Material (14 : Basis) (59 : Basis) where
  plus := ![v1311_pa,v1311_pb,v1311_pg]
  minus := ![(Primitive.Addresses.material1311 1).one,v1311_mb,v1311_mg]
  upper := v1311_upper
  lower := (Primitive.Addresses.material1311 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1311_pa_checked.trans (by decide +kernel)
    · exact v1311_pb_checked.trans (by decide +kernel)
    · exact v1311_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 59 Primitive.Addresses.material1311
    · exact v1311_mb_checked.trans (by decide +kernel)
    · exact v1311_mg_checked.trans (by decide +kernel)
  upper_error := v1311_upper_checked
  lower_error := reuse_lower_error 14 59 Primitive.Addresses.material1311

def v1312_pa : Scalar.QComplex := ((999999739168189840783536514420 : Int)/10^30,(-722262800014786678780497109 : Int)/10^30)
theorem v1312_pa_checked : Scalar.distance (sourceCoefficient 14 60 1 0) v1312_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1312_pb : Scalar.QComplex := ((-311640139467619286746506 : Int)/10^30,(-431477376621885377133545143 : Int)/10^30)
theorem v1312_pb_checked : Scalar.distance (sourceCoefficient 14 60 1 1) v1312_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1312_pg : Scalar.QComplex := ((-93086402182976176815291 : Int)/10^30,(67232863020448288338 : Int)/10^30)
theorem v1312_pg_checked : Scalar.distance (sourceCoefficient 14 60 1 2) v1312_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1312_mb : Scalar.QComplex := ((-683985566434784334455556 : Int)/10^30,(-431476947031733960826029007 : Int)/10^30)
theorem v1312_mb_checked : Scalar.distance (sourceCoefficient 14 60 3 1) v1312_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1312_mg : Scalar.QComplex := ((-93086309503721654445708 : Int)/10^30,(147562210614566090911 : Int)/10^30)
theorem v1312_mg_checked : Scalar.distance (sourceCoefficient 14 60 3 2) v1312_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1312_upper : Scalar.QComplex := ((999997003225976914676557390268 : Int)/10^30,(-2448170554825807361120401988 : Int)/10^30)
theorem v1312_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 60 5) 1) 14) v1312_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1312 : Material (14 : Basis) (60 : Basis) where
  plus := ![v1312_pa,v1312_pb,v1312_pg]
  minus := ![(Primitive.Addresses.material1312 1).one,v1312_mb,v1312_mg]
  upper := v1312_upper
  lower := (Primitive.Addresses.material1312 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1312_pa_checked.trans (by decide +kernel)
    · exact v1312_pb_checked.trans (by decide +kernel)
    · exact v1312_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 60 Primitive.Addresses.material1312
    · exact v1312_mb_checked.trans (by decide +kernel)
    · exact v1312_mg_checked.trans (by decide +kernel)
  upper_error := v1312_upper_checked
  lower_error := reuse_lower_error 14 60 Primitive.Addresses.material1312

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
