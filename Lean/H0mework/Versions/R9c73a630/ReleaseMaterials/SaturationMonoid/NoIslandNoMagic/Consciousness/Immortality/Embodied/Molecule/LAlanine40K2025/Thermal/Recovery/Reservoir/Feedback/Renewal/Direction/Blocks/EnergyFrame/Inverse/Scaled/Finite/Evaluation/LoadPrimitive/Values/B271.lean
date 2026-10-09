import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B180
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B181

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4337_pa : Scalar.QComplex := ((999997665361210916111748062326 : Int)/10^30,(-2160849862352657996159042370 : Int)/10^30)
theorem v4337_pa_checked : Scalar.distance (sourceCoefficient 68 88 1 0) v4337_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4337_pb : Scalar.QComplex := ((-932358121772327648238558 : Int)/10^30,(-431476504359157370159807063 : Int)/10^30)
theorem v4337_pb_checked : Scalar.distance (sourceCoefficient 68 88 1 1) v4337_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4337_pg : Scalar.QComplex := ((-93086211570887930894665 : Int)/10^30,(201145797062663669224 : Int)/10^30)
theorem v4337_pg_checked : Scalar.distance (sourceCoefficient 68 88 1 2) v4337_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4337_mb : Scalar.QComplex := ((-1304702564894370655609080 : Int)/10^30,(-431475539117668108310773455 : Int)/10^30)
theorem v4337_mb_checked : Scalar.distance (sourceCoefficient 68 88 3 1) v4337_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4337_mg : Scalar.QComplex := ((-93086003330873518345114 : Int)/10^30,(281474930305228697995 : Int)/10^30)
theorem v4337_mg_checked : Scalar.distance (sourceCoefficient 68 88 3 2) v4337_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4337_upper : Scalar.QComplex := ((999992446551324685553379774604 : Int)/10^30,(-3886751895354526308882994019 : Int)/10^30)
theorem v4337_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 68 88 5) 1) 14) v4337_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4337 : Material (68 : Basis) (88 : Basis) where
  plus := ![v4337_pa,v4337_pb,v4337_pg]
  minus := ![(Primitive.Addresses.material4337 1).one,v4337_mb,v4337_mg]
  upper := v4337_upper
  lower := (Primitive.Addresses.material4337 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4337_pa_checked.trans (by decide +kernel)
    · exact v4337_pb_checked.trans (by decide +kernel)
    · exact v4337_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 68 88 Primitive.Addresses.material4337
    · exact v4337_mb_checked.trans (by decide +kernel)
    · exact v4337_mg_checked.trans (by decide +kernel)
  upper_error := v4337_upper_checked
  lower_error := reuse_lower_error 68 88 Primitive.Addresses.material4337

def v4338_pa : Scalar.QComplex := ((999997630464815037281491421609 : Int)/10^30,(-2176939309036529902141345035 : Int)/10^30)
theorem v4338_pa_checked : Scalar.distance (sourceCoefficient 68 89 1 0) v4338_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4338_pb : Scalar.QComplex := ((-939300354340293840322355 : Int)/10^30,(-431476488451471657057450851 : Int)/10^30)
theorem v4338_pb_checked : Scalar.distance (sourceCoefficient 68 89 1 1) v4338_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4338_pg : Scalar.QComplex := ((-93086208230745198066710 : Int)/10^30,(202643505997586459597 : Int)/10^30)
theorem v4338_pg_checked : Scalar.distance (sourceCoefficient 68 89 1 2) v4338_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4338_mb : Scalar.QComplex := ((-1311644781149810072098074 : Int)/10^30,(-431475517219154278760134966 : Int)/10^30)
theorem v4338_mb_checked : Scalar.distance (sourceCoefficient 68 89 3 1) v4338_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4338_mg : Scalar.QComplex := ((-93085998698276672672990 : Int)/10^30,(282972635800093259229 : Int)/10^30)
theorem v4338_mg_checked : Scalar.distance (sourceCoefficient 68 89 3 2) v4338_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4338_upper : Scalar.QComplex := ((999992383886055427643866443940 : Int)/10^30,(-3902841257847043867854198142 : Int)/10^30)
theorem v4338_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 68 89 5) 1) 14) v4338_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4338 : Material (68 : Basis) (89 : Basis) where
  plus := ![v4338_pa,v4338_pb,v4338_pg]
  minus := ![(Primitive.Addresses.material4338 1).one,v4338_mb,v4338_mg]
  upper := v4338_upper
  lower := (Primitive.Addresses.material4338 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4338_pa_checked.trans (by decide +kernel)
    · exact v4338_pb_checked.trans (by decide +kernel)
    · exact v4338_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 68 89 Primitive.Addresses.material4338
    · exact v4338_mb_checked.trans (by decide +kernel)
    · exact v4338_mg_checked.trans (by decide +kernel)
  upper_error := v4338_upper_checked
  lower_error := reuse_lower_error 68 89 Primitive.Addresses.material4338

def v4339_pa : Scalar.QComplex := ((999997573079305022104259908102 : Int)/10^30,(-2203142187878878544759788453 : Int)/10^30)
theorem v4339_pa_checked : Scalar.distance (sourceCoefficient 68 90 1 0) v4339_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4339_pb : Scalar.QComplex := ((-950606304052570822773235 : Int)/10^30,(-431476462225832424641435253 : Int)/10^30)
theorem v4339_pb_checked : Scalar.distance (sourceCoefficient 68 90 1 1) v4339_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4339_pg : Scalar.QComplex := ((-93086202730895488842562 : Int)/10^30,(205082638065180427198 : Int)/10^30)
theorem v4339_pg_checked : Scalar.distance (sourceCoefficient 68 90 1 2) v4339_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4339_mb : Scalar.QComplex := ((-1322950704020819770609842 : Int)/10^30,(-431475481236999410725749289 : Int)/10^30)
theorem v4339_mb_checked : Scalar.distance (sourceCoefficient 68 90 3 1) v4339_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4339_mg : Scalar.QComplex := ((-93085991093567891390986 : Int)/10^30,(285411762213364289199 : Int)/10^30)
theorem v4339_mg_checked : Scalar.distance (sourceCoefficient 68 90 3 2) v4339_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4339_upper : Scalar.QComplex := ((999992281276839106148709989297 : Int)/10^30,(-3929043998621098167767162561 : Int)/10^30)
theorem v4339_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 68 90 5) 1) 14) v4339_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4339 : Material (68 : Basis) (90 : Basis) where
  plus := ![v4339_pa,v4339_pb,v4339_pg]
  minus := ![(Primitive.Addresses.material4339 1).one,v4339_mb,v4339_mg]
  upper := v4339_upper
  lower := (Primitive.Addresses.material4339 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4339_pa_checked.trans (by decide +kernel)
    · exact v4339_pb_checked.trans (by decide +kernel)
    · exact v4339_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 68 90 Primitive.Addresses.material4339
    · exact v4339_mb_checked.trans (by decide +kernel)
    · exact v4339_mg_checked.trans (by decide +kernel)
  upper_error := v4339_upper_checked
  lower_error := reuse_lower_error 68 90 Primitive.Addresses.material4339

def v4340_pa : Scalar.QComplex := ((999997540449622447673438168955 : Int)/10^30,(-2217903222802246934385479023 : Int)/10^30)
theorem v4340_pa_checked : Scalar.distance (sourceCoefficient 68 91 1 0) v4340_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4340_pb : Scalar.QComplex := ((-956975356710329636491709 : Int)/10^30,(-431476447278040463678859775 : Int)/10^30)
theorem v4340_pb_checked : Scalar.distance (sourceCoefficient 68 91 1 1) v4340_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4340_pg : Scalar.QComplex := ((-93086199599796029444824 : Int)/10^30,(206456689881430388587 : Int)/10^30)
theorem v4340_pg_checked : Scalar.distance (sourceCoefficient 68 91 1 2) v4340_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4340_mb : Scalar.QComplex := ((-1329319741407817961006588 : Int)/10^30,(-431475460793007423346690344 : Int)/10^30)
theorem v4340_mb_checked : Scalar.distance (sourceCoefficient 68 91 3 1) v4340_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4340_mg : Scalar.QComplex := ((-93085986776724765417483 : Int)/10^30,(286785810815994148152 : Int)/10^30)
theorem v4340_mg_checked : Scalar.distance (sourceCoefficient 68 91 3 2) v4340_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4340_upper : Scalar.QComplex := ((999992223170997962690980420946 : Int)/10^30,(-3943804955243767010213484337 : Int)/10^30)
theorem v4340_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 68 91 5) 1) 14) v4340_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4340 : Material (68 : Basis) (91 : Basis) where
  plus := ![v4340_pa,v4340_pb,v4340_pg]
  minus := ![(Primitive.Addresses.material4340 1).one,v4340_mb,v4340_mg]
  upper := v4340_upper
  lower := (Primitive.Addresses.material4340 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4340_pa_checked.trans (by decide +kernel)
    · exact v4340_pb_checked.trans (by decide +kernel)
    · exact v4340_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 68 91 Primitive.Addresses.material4340
    · exact v4340_mb_checked.trans (by decide +kernel)
    · exact v4340_mg_checked.trans (by decide +kernel)
  upper_error := v4340_upper_checked
  lower_error := reuse_lower_error 68 91 Primitive.Addresses.material4340

def v4341_pa : Scalar.QComplex := ((999997469063479937169948600218 : Int)/10^30,(-2249859247705507357801765858 : Int)/10^30)
theorem v4341_pa_checked : Scalar.distance (sourceCoefficient 68 92 1 0) v4341_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4341_pb : Scalar.QComplex := ((-970763658244447687415119 : Int)/10^30,(-431476414488271719697872022 : Int)/10^30)
theorem v4341_pb_checked : Scalar.distance (sourceCoefficient 68 92 1 1) v4341_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4341_pg : Scalar.QComplex := ((-93086192740243257308490 : Int)/10^30,(209431361627815145695 : Int)/10^30)
theorem v4341_pg_checked : Scalar.distance (sourceCoefficient 68 92 1 2) v4341_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4341_mb : Scalar.QComplex := ((-1343108009511827564574755 : Int)/10^30,(-431475416104567666599711529 : Int)/10^30)
theorem v4341_mb_checked : Scalar.distance (sourceCoefficient 68 92 3 1) v4341_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4341_mg : Scalar.QComplex := ((-93085977350166804518197 : Int)/10^30,(289760475535287565301 : Int)/10^30)
theorem v4341_mg_checked : Scalar.distance (sourceCoefficient 68 92 3 2) v4341_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4341_upper : Scalar.QComplex := ((999992096631761818366924419737 : Int)/10^30,(-3975760809346276285730877160 : Int)/10^30)
theorem v4341_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 68 92 5) 1) 14) v4341_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4341 : Material (68 : Basis) (92 : Basis) where
  plus := ![v4341_pa,v4341_pb,v4341_pg]
  minus := ![(Primitive.Addresses.material4341 1).one,v4341_mb,v4341_mg]
  upper := v4341_upper
  lower := (Primitive.Addresses.material4341 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4341_pa_checked.trans (by decide +kernel)
    · exact v4341_pb_checked.trans (by decide +kernel)
    · exact v4341_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 68 92 Primitive.Addresses.material4341
    · exact v4341_mb_checked.trans (by decide +kernel)
    · exact v4341_mg_checked.trans (by decide +kernel)
  upper_error := v4341_upper_checked
  lower_error := reuse_lower_error 68 92 Primitive.Addresses.material4341

def v4342_pa : Scalar.QComplex := ((999997383017017558370248314699 : Int)/10^30,(-2287784761791049502199527595 : Int)/10^30)
theorem v4342_pa_checked : Scalar.distance (sourceCoefficient 68 93 1 0) v4342_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4342_pb : Scalar.QComplex := ((-987127658661508798445480 : Int)/10^30,(-431476374810901807699423263 : Int)/10^30)
theorem v4342_pb_checked : Scalar.distance (sourceCoefficient 68 93 1 1) v4342_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4342_pg : Scalar.QComplex := ((-93086184455390762240581 : Int)/10^30,(212961711647489143150 : Int)/10^30)
theorem v4342_pg_checked : Scalar.distance (sourceCoefficient 68 93 1 2) v4342_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4342_mb : Scalar.QComplex := ((-1359471969596040216918117 : Int)/10^30,(-431475362305817175595477987 : Int)/10^30)
theorem v4342_mb_checked : Scalar.distance (sourceCoefficient 68 93 3 1) v4342_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4342_mg : Scalar.QComplex := ((-93085966018784328363339 : Int)/10^30,(293290817090996338126 : Int)/10^30)
theorem v4342_mg_checked : Scalar.distance (sourceCoefficient 68 93 3 2) v4342_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4342_upper : Scalar.QComplex := ((999991945129430859781006088165 : Int)/10^30,(-4013686118437832251828880797 : Int)/10^30)
theorem v4342_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 68 93 5) 1) 14) v4342_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4342 : Material (68 : Basis) (93 : Basis) where
  plus := ![v4342_pa,v4342_pb,v4342_pg]
  minus := ![(Primitive.Addresses.material4342 1).one,v4342_mb,v4342_mg]
  upper := v4342_upper
  lower := (Primitive.Addresses.material4342 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4342_pa_checked.trans (by decide +kernel)
    · exact v4342_pb_checked.trans (by decide +kernel)
    · exact v4342_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 68 93 Primitive.Addresses.material4342
    · exact v4342_mb_checked.trans (by decide +kernel)
    · exact v4342_mg_checked.trans (by decide +kernel)
  upper_error := v4342_upper_checked
  lower_error := reuse_lower_error 68 93 Primitive.Addresses.material4342

def v4343_pa : Scalar.QComplex := ((999997279524107650483358677807 : Int)/10^30,(-2332583199740140550544564129 : Int)/10^30)
theorem v4343_pa_checked : Scalar.distance (sourceCoefficient 68 94 1 0) v4343_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4343_pb : Scalar.QComplex := ((-1006457169201615594103865 : Int)/10^30,(-431476326877117737761965379 : Int)/10^30)
theorem v4343_pb_checked : Scalar.distance (sourceCoefficient 68 94 1 1) v4343_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4343_pg : Scalar.QComplex := ((-93086174467910189661417 : Int)/10^30,(217131837393856017004 : Int)/10^30)
theorem v4343_pg_checked : Scalar.distance (sourceCoefficient 68 94 1 2) v4343_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4343_mb : Scalar.QComplex := ((-1378801431574190041360028 : Int)/10^30,(-431475297691553926322038921 : Int)/10^30)
theorem v4343_mb_checked : Scalar.distance (sourceCoefficient 68 94 3 1) v4343_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4343_mg : Scalar.QComplex := ((-93085952432676770956607 : Int)/10^30,(297460932665888897737 : Int)/10^30)
theorem v4343_mg_checked : Scalar.distance (sourceCoefficient 68 94 3 2) v4343_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4343_upper : Scalar.QComplex := ((999991764318635274839014539965 : Int)/10^30,(-4058484311045538671620094869 : Int)/10^30)
theorem v4343_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 68 94 5) 1) 14) v4343_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4343 : Material (68 : Basis) (94 : Basis) where
  plus := ![v4343_pa,v4343_pb,v4343_pg]
  minus := ![(Primitive.Addresses.material4343 1).one,v4343_mb,v4343_mg]
  upper := v4343_upper
  lower := (Primitive.Addresses.material4343 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4343_pa_checked.trans (by decide +kernel)
    · exact v4343_pb_checked.trans (by decide +kernel)
    · exact v4343_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 68 94 Primitive.Addresses.material4343
    · exact v4343_mb_checked.trans (by decide +kernel)
    · exact v4343_mg_checked.trans (by decide +kernel)
  upper_error := v4343_upper_checked
  lower_error := reuse_lower_error 68 94 Primitive.Addresses.material4343

def v4344_pa : Scalar.QComplex := ((999997175270696586283649594566 : Int)/10^30,(-2376857300666532470465811409 : Int)/10^30)
theorem v4344_pa_checked : Scalar.distance (sourceCoefficient 68 95 1 0) v4344_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4344_pb : Scalar.QComplex := ((-1025560439238726568145408 : Int)/10^30,(-431476278369975546661131947 : Int)/10^30)
theorem v4344_pb_checked : Scalar.distance (sourceCoefficient 68 95 1 1) v4344_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4344_pg : Scalar.QComplex := ((-93086164383185659643590 : Int)/10^30,(221253154385488448900 : Int)/10^30)
theorem v4344_pg_checked : Scalar.distance (sourceCoefficient 68 95 1 2) v4344_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4344_mb : Scalar.QComplex := ((-1397904652638801487679405 : Int)/10^30,(-431475232699168133964047497 : Int)/10^30)
theorem v4344_mb_checked : Scalar.distance (sourceCoefficient 68 95 3 1) v4344_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4344_mg : Scalar.QComplex := ((-93085938791445049390697 : Int)/10^30,(301582239420303589884 : Int)/10^30)
theorem v4344_mg_checked : Scalar.distance (sourceCoefficient 68 95 3 2) v4344_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4344_upper : Scalar.QComplex := ((999991583652297799956914313264 : Int)/10^30,(-4102758166098928361674553668 : Int)/10^30)
theorem v4344_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 68 95 5) 1) 14) v4344_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4344 : Material (68 : Basis) (95 : Basis) where
  plus := ![v4344_pa,v4344_pb,v4344_pg]
  minus := ![(Primitive.Addresses.material4344 1).one,v4344_mb,v4344_mg]
  upper := v4344_upper
  lower := (Primitive.Addresses.material4344 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4344_pa_checked.trans (by decide +kernel)
    · exact v4344_pb_checked.trans (by decide +kernel)
    · exact v4344_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 68 95 Primitive.Addresses.material4344
    · exact v4344_mb_checked.trans (by decide +kernel)
    · exact v4344_mg_checked.trans (by decide +kernel)
  upper_error := v4344_upper_checked
  lower_error := reuse_lower_error 68 95 Primitive.Addresses.material4344

def v4345_pa : Scalar.QComplex := ((999997124502892963506463119418 : Int)/10^30,(-2398121336711171188631597973 : Int)/10^30)
theorem v4345_pa_checked : Scalar.distance (sourceCoefficient 68 96 1 0) v4345_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4345_pb : Scalar.QComplex := ((-1034735387991790116167471 : Int)/10^30,(-431476254672012107309774896 : Int)/10^30)
theorem v4345_pb_checked : Scalar.distance (sourceCoefficient 68 96 1 1) v4345_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4345_pg : Scalar.QComplex := ((-93086159464004114378761 : Int)/10^30,(223232547067670074828 : Int)/10^30)
theorem v4345_pg_checked : Scalar.distance (sourceCoefficient 68 96 1 2) v4345_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4345_mb : Scalar.QComplex := ((-1407079577525337167555700 : Int)/10^30,(-431475201083645968905916389 : Int)/10^30)
theorem v4345_mb_checked : Scalar.distance (sourceCoefficient 68 96 3 1) v4345_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4345_mg : Scalar.QComplex := ((-93085932164138599576288 : Int)/10^30,(303561627120434735670 : Int)/10^30)
theorem v4345_mg_checked : Scalar.distance (sourceCoefficient 68 96 3 2) v4345_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4345_upper : Scalar.QComplex := ((999991496184772635094184571214 : Int)/10^30,(-4124022082852659806743216576 : Int)/10^30)
theorem v4345_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 68 96 5) 1) 14) v4345_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4345 : Material (68 : Basis) (96 : Basis) where
  plus := ![v4345_pa,v4345_pb,v4345_pg]
  minus := ![(Primitive.Addresses.material4345 1).one,v4345_mb,v4345_mg]
  upper := v4345_upper
  lower := (Primitive.Addresses.material4345 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4345_pa_checked.trans (by decide +kernel)
    · exact v4345_pb_checked.trans (by decide +kernel)
    · exact v4345_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 68 96 Primitive.Addresses.material4345
    · exact v4345_mb_checked.trans (by decide +kernel)
    · exact v4345_mg_checked.trans (by decide +kernel)
  upper_error := v4345_upper_checked
  lower_error := reuse_lower_error 68 96 Primitive.Addresses.material4345

def v4346_pa : Scalar.QComplex := ((999996946374656614575269636144 : Int)/10^30,(-2471283343152523191662072181 : Int)/10^30)
theorem v4346_pa_checked : Scalar.distance (sourceCoefficient 68 97 1 0) v4346_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4346_pb : Scalar.QComplex := ((-1066303130816775909831484 : Int)/10^30,(-431476171148498609756938588 : Int)/10^30)
theorem v4346_pb_checked : Scalar.distance (sourceCoefficient 68 97 1 1) v4346_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4346_pg : Scalar.QComplex := ((-93086142163713262006187 : Int)/10^30,(230042935072448962924 : Int)/10^30)
theorem v4346_pg_checked : Scalar.distance (sourceCoefficient 68 97 1 2) v4346_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4346_mb : Scalar.QComplex := ((-1438647236519179201375488 : Int)/10^30,(-431475090318623271370314657 : Int)/10^30)
theorem v4346_mb_checked : Scalar.distance (sourceCoefficient 68 97 3 1) v4346_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4346_mg : Scalar.QComplex := ((-93085908986796069257918 : Int)/10^30,(310371997660023090057 : Int)/10^30)
theorem v4346_mg_checked : Scalar.distance (sourceCoefficient 68 97 3 2) v4346_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4346_upper : Scalar.QComplex := ((999991191785815674850419414927 : Int)/10^30,(-4197183672894621157480959582 : Int)/10^30)
theorem v4346_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 68 97 5) 1) 14) v4346_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4346 : Material (68 : Basis) (97 : Basis) where
  plus := ![v4346_pa,v4346_pb,v4346_pg]
  minus := ![(Primitive.Addresses.material4346 1).one,v4346_mb,v4346_mg]
  upper := v4346_upper
  lower := (Primitive.Addresses.material4346 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4346_pa_checked.trans (by decide +kernel)
    · exact v4346_pb_checked.trans (by decide +kernel)
    · exact v4346_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 68 97 Primitive.Addresses.material4346
    · exact v4346_mb_checked.trans (by decide +kernel)
    · exact v4346_mg_checked.trans (by decide +kernel)
  upper_error := v4346_upper_checked
  lower_error := reuse_lower_error 68 97 Primitive.Addresses.material4346

def v4347_pa : Scalar.QComplex := ((999998272450071210244239506927 : Int)/10^30,(-1858789087860899580306928784 : Int)/10^30)
theorem v4347_pa_checked : Scalar.distance (sourceCoefficient 69 70 1 0) v4347_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4347_pb : Scalar.QComplex := ((-802025707666210428656525 : Int)/10^30,(-431476775587126140323678778 : Int)/10^30)
theorem v4347_pb_checked : Scalar.distance (sourceCoefficient 69 70 1 1) v4347_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4347_pg : Scalar.QComplex := ((-93086269083949500709177 : Int)/10^30,(173028040117507132394 : Int)/10^30)
theorem v4347_pg_checked : Scalar.distance (sourceCoefficient 69 70 1 2) v4347_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4347_mb : Scalar.QComplex := ((-1174370433374489087719909 : Int)/10^30,(-431475922816539307456898635 : Int)/10^30)
theorem v4347_mb_checked : Scalar.distance (sourceCoefficient 69 70 3 1) v4347_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4347_mg : Scalar.QComplex := ((-93086085108271540325723 : Int)/10^30,(253357233460779959435 : Int)/10^30)
theorem v4347_mg_checked : Scalar.distance (sourceCoefficient 69 70 3 2) v4347_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4347_upper : Scalar.QComplex := ((999993574968774825513716624294 : Int)/10^30,(-3584692618527107143906488625 : Int)/10^30)
theorem v4347_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 69 70 5) 1) 14) v4347_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4347 : Material (69 : Basis) (70 : Basis) where
  plus := ![v4347_pa,v4347_pb,v4347_pg]
  minus := ![(Primitive.Addresses.material4347 1).one,v4347_mb,v4347_mg]
  upper := v4347_upper
  lower := (Primitive.Addresses.material4347 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4347_pa_checked.trans (by decide +kernel)
    · exact v4347_pb_checked.trans (by decide +kernel)
    · exact v4347_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 69 70 Primitive.Addresses.material4347
    · exact v4347_mb_checked.trans (by decide +kernel)
    · exact v4347_mg_checked.trans (by decide +kernel)
  upper_error := v4347_upper_checked
  lower_error := reuse_lower_error 69 70 Primitive.Addresses.material4347

def v4348_pa : Scalar.QComplex := ((999998226999779020189010031090 : Int)/10^30,(-1883081861850365331981734750 : Int)/10^30)
theorem v4348_pa_checked : Scalar.distance (sourceCoefficient 69 71 1 0) v4348_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4348_pb : Scalar.QComplex := ((-812507493391507441416061 : Int)/10^30,(-431476755884182581354701550 : Int)/10^30)
theorem v4348_pb_checked : Scalar.distance (sourceCoefficient 69 71 1 1) v4348_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4348_pg : Scalar.QComplex := ((-93086264843202372197824 : Int)/10^30,(175289367701721399308 : Int)/10^30)
theorem v4348_pg_checked : Scalar.distance (sourceCoefficient 69 71 1 2) v4348_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4348_mb : Scalar.QComplex := ((-1184852198194185329924893 : Int)/10^30,(-431475894068294085967511314 : Int)/10^30)
theorem v4348_mb_checked : Scalar.distance (sourceCoefficient 69 71 3 1) v4348_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4348_mg : Scalar.QComplex := ((-93086078916102132075102 : Int)/10^30,(255618556543424843224 : Int)/10^30)
theorem v4348_mg_checked : Scalar.distance (sourceCoefficient 69 71 3 2) v4348_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4348_upper : Scalar.QComplex := ((999993487591426245752852405914 : Int)/10^30,(-3608985277892258566224754551 : Int)/10^30)
theorem v4348_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 69 71 5) 1) 14) v4348_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4348 : Material (69 : Basis) (71 : Basis) where
  plus := ![v4348_pa,v4348_pb,v4348_pg]
  minus := ![(Primitive.Addresses.material4348 1).one,v4348_mb,v4348_mg]
  upper := v4348_upper
  lower := (Primitive.Addresses.material4348 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4348_pa_checked.trans (by decide +kernel)
    · exact v4348_pb_checked.trans (by decide +kernel)
    · exact v4348_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 69 71 Primitive.Addresses.material4348
    · exact v4348_mb_checked.trans (by decide +kernel)
    · exact v4348_mg_checked.trans (by decide +kernel)
  upper_error := v4348_upper_checked
  lower_error := reuse_lower_error 69 71 Primitive.Addresses.material4348

def v4349_pa : Scalar.QComplex := ((999998177009302436809884041193 : Int)/10^30,(-1909444440624365700214164794 : Int)/10^30)
theorem v4349_pa_checked : Scalar.distance (sourceCoefficient 69 72 1 0) v4349_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4349_pb : Scalar.QComplex := ((-823882353150936852091136 : Int)/10^30,(-431476734118365810234460402 : Int)/10^30)
theorem v4349_pb_checked : Scalar.distance (sourceCoefficient 69 72 1 1) v4349_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4349_pg : Scalar.QComplex := ((-93086260168619600378556 : Int)/10^30,(177743366001986801620 : Int)/10^30)
theorem v4349_pg_checked : Scalar.distance (sourceCoefficient 69 72 1 2) v4349_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4349_mb : Scalar.QComplex := ((-1196227034935315017912252 : Int)/10^30,(-431475862486493751533941179 : Int)/10^30)
theorem v4349_mb_checked : Scalar.distance (sourceCoefficient 69 72 3 1) v4349_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4349_mg : Scalar.QComplex := ((-93086072123831091668198 : Int)/10^30,(258072549896000128397 : Int)/10^30)
theorem v4349_mg_checked : Scalar.distance (sourceCoefficient 69 72 3 2) v4349_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4349_upper : Scalar.QComplex := ((999993392101604747855934507156 : Int)/10^30,(-3635347731123267134319390556 : Int)/10^30)
theorem v4349_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 69 72 5) 1) 14) v4349_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4349 : Material (69 : Basis) (72 : Basis) where
  plus := ![v4349_pa,v4349_pb,v4349_pg]
  minus := ![(Primitive.Addresses.material4349 1).one,v4349_mb,v4349_mg]
  upper := v4349_upper
  lower := (Primitive.Addresses.material4349 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4349_pa_checked.trans (by decide +kernel)
    · exact v4349_pb_checked.trans (by decide +kernel)
    · exact v4349_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 69 72 Primitive.Addresses.material4349
    · exact v4349_mb_checked.trans (by decide +kernel)
    · exact v4349_mg_checked.trans (by decide +kernel)
  upper_error := v4349_upper_checked
  lower_error := reuse_lower_error 69 72 Primitive.Addresses.material4349

def v4350_pa : Scalar.QComplex := ((999998158921087059376399237612 : Int)/10^30,(-1918894065942589631962826525 : Int)/10^30)
theorem v4350_pa_checked : Scalar.distance (sourceCoefficient 69 73 1 0) v4350_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4350_pb : Scalar.QComplex := ((-827959653873221048057553 : Int)/10^30,(-431476726219097482009974734 : Int)/10^30)
theorem v4350_pb_checked : Scalar.distance (sourceCoefficient 69 73 1 1) v4350_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4350_pg : Scalar.QComplex := ((-93086258474646685471177 : Int)/10^30,(178622997866832358702 : Int)/10^30)
theorem v4350_pg_checked : Scalar.distance (sourceCoefficient 69 73 1 2) v4350_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4350_mb : Scalar.QComplex := ((-1200304327322721015704756 : Int)/10^30,(-431475851068701476044494577 : Int)/10^30)
theorem v4350_mb_checked : Scalar.distance (sourceCoefficient 69 73 3 1) v4350_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4350_mg : Scalar.QComplex := ((-93086069670776125291173 : Int)/10^30,(258952179971496209178 : Int)/10^30)
theorem v4350_mg_checked : Scalar.distance (sourceCoefficient 69 73 3 2) v4350_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4350_upper : Scalar.QComplex := ((999993357704220274752252932511 : Int)/10^30,(-3644797311148765394169254366 : Int)/10^30)
theorem v4350_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 69 73 5) 1) 14) v4350_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4350 : Material (69 : Basis) (73 : Basis) where
  plus := ![v4350_pa,v4350_pb,v4350_pg]
  minus := ![(Primitive.Addresses.material4350 1).one,v4350_mb,v4350_mg]
  upper := v4350_upper
  lower := (Primitive.Addresses.material4350 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4350_pa_checked.trans (by decide +kernel)
    · exact v4350_pb_checked.trans (by decide +kernel)
    · exact v4350_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 69 73 Primitive.Addresses.material4350
    · exact v4350_mb_checked.trans (by decide +kernel)
    · exact v4350_mg_checked.trans (by decide +kernel)
  upper_error := v4350_upper_checked
  lower_error := reuse_lower_error 69 73 Primitive.Addresses.material4350

def v4351_pa : Scalar.QComplex := ((999998138460626768956668424797 : Int)/10^30,(-1929527216997274846609419949 : Int)/10^30)
theorem v4351_pa_checked : Scalar.distance (sourceCoefficient 69 74 1 0) v4351_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4351_pb : Scalar.QComplex := ((-832547619291448763526802 : Int)/10^30,(-431476717269052755198846807 : Int)/10^30)
theorem v4351_pb_checked : Scalar.distance (sourceCoefficient 69 74 1 1) v4351_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4351_pg : Scalar.QComplex := ((-93086256556915261521850 : Int)/10^30,(179612799911258003417 : Int)/10^30)
theorem v4351_pg_checked : Scalar.distance (sourceCoefficient 69 74 1 2) v4351_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4351_mb : Scalar.QComplex := ((-1204892283309154021402693 : Int)/10^30,(-431475838159452560105348746 : Int)/10^30)
theorem v4351_mb_checked : Scalar.distance (sourceCoefficient 69 74 3 1) v4351_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4351_mg : Scalar.QComplex := ((-93086066898890830090797 : Int)/10^30,(259941979992457469115 : Int)/10^30)
theorem v4351_mg_checked : Scalar.distance (sourceCoefficient 69 74 3 2) v4351_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4351_upper : Scalar.QComplex := ((999993318891936369326379663425 : Int)/10^30,(-3655430411053722867720196601 : Int)/10^30)
theorem v4351_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 69 74 5) 1) 14) v4351_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4351 : Material (69 : Basis) (74 : Basis) where
  plus := ![v4351_pa,v4351_pb,v4351_pg]
  minus := ![(Primitive.Addresses.material4351 1).one,v4351_mb,v4351_mg]
  upper := v4351_upper
  lower := (Primitive.Addresses.material4351 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4351_pa_checked.trans (by decide +kernel)
    · exact v4351_pb_checked.trans (by decide +kernel)
    · exact v4351_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 69 74 Primitive.Addresses.material4351
    · exact v4351_mb_checked.trans (by decide +kernel)
    · exact v4351_mg_checked.trans (by decide +kernel)
  upper_error := v4351_upper_checked
  lower_error := reuse_lower_error 69 74 Primitive.Addresses.material4351

def v4352_pa : Scalar.QComplex := ((999998109764688436001205467870 : Int)/10^30,(-1944342318147312378147540823 : Int)/10^30)
theorem v4352_pa_checked : Scalar.distance (sourceCoefficient 69 75 1 0) v4352_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4352_pb : Scalar.QComplex := ((-838940002018627465879804 : Int)/10^30,(-431476704690562367945389568 : Int)/10^30)
theorem v4352_pb_checked : Scalar.distance (sourceCoefficient 69 75 1 1) v4352_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4352_pg : Scalar.QComplex := ((-93086253864480010027034 : Int)/10^30,(180991884743763927174 : Int)/10^30)
theorem v4352_pg_checked : Scalar.distance (sourceCoefficient 69 75 1 2) v4352_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4352_mb : Scalar.QComplex := ((-1211284652801485798081424 : Int)/10^30,(-431475820064628465074106922 : Int)/10^30)
theorem v4352_mb_checked : Scalar.distance (sourceCoefficient 69 75 3 1) v4352_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4352_mg : Scalar.QComplex := ((-93086063016368482335226 : Int)/10^30,(261321061988016723181 : Int)/10^30)
theorem v4352_mg_checked : Scalar.distance (sourceCoefficient 69 75 3 2) v4352_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4352_upper : Scalar.QComplex := ((999993264626520206112881158355 : Int)/10^30,(-3670245440611821252816955001 : Int)/10^30)
theorem v4352_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 69 75 5) 1) 14) v4352_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4352 : Material (69 : Basis) (75 : Basis) where
  plus := ![v4352_pa,v4352_pb,v4352_pg]
  minus := ![(Primitive.Addresses.material4352 1).one,v4352_mb,v4352_mg]
  upper := v4352_upper
  lower := (Primitive.Addresses.material4352 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4352_pa_checked.trans (by decide +kernel)
    · exact v4352_pb_checked.trans (by decide +kernel)
    · exact v4352_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 69 75 Primitive.Addresses.material4352
    · exact v4352_mb_checked.trans (by decide +kernel)
    · exact v4352_mg_checked.trans (by decide +kernel)
  upper_error := v4352_upper_checked
  lower_error := reuse_lower_error 69 75 Primitive.Addresses.material4352

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
