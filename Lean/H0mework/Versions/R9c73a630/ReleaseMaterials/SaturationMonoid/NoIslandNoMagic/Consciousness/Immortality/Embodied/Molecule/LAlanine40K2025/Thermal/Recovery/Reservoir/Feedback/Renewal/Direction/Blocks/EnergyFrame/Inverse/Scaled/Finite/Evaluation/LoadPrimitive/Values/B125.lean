import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B083
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B084

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2001_pa : Scalar.QComplex := ((999999757824786056129646282313 : Int)/10^30,(-695952849867651924019335670 : Int)/10^30)
theorem v2001_pa_checked : Scalar.distance (sourceCoefficient 23 47 1 0) v2001_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2001_pb : Scalar.QComplex := ((-300288004070443759440264 : Int)/10^30,(-431477407420973035176198560 : Int)/10^30)
theorem v2001_pb_checked : Scalar.distance (sourceCoefficient 23 47 1 1) v2001_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2001_pg : Scalar.QComplex := ((-93086406373592797677164 : Int)/10^30,(64783765488662532806 : Int)/10^30)
theorem v2001_pg_checked : Scalar.distance (sourceCoefficient 23 47 1 2) v2001_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2001_mb : Scalar.QComplex := ((-672633461842753143211281 : Int)/10^30,(-431476987627191717524601011 : Int)/10^30)
theorem v2001_mb_checked : Scalar.distance (sourceCoefficient 23 47 3 1) v2001_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2001_mg : Scalar.QComplex := ((-93086315807797581622417 : Int)/10^30,(145113117611004681187 : Int)/10^30)
theorem v2001_mg_checked : Scalar.distance (sourceCoefficient 23 47 3 2) v2001_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2001_upper : Scalar.QComplex := ((999997067291132477136215689635 : Int)/10^30,(-2421860676063845321170417910 : Int)/10^30)
theorem v2001_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 47 5) 1) 14) v2001_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2001 : Material (23 : Basis) (47 : Basis) where
  plus := ![v2001_pa,v2001_pb,v2001_pg]
  minus := ![(Primitive.Addresses.material2001 1).one,v2001_mb,v2001_mg]
  upper := v2001_upper
  lower := (Primitive.Addresses.material2001 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2001_pa_checked.trans (by decide +kernel)
    · exact v2001_pb_checked.trans (by decide +kernel)
    · exact v2001_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 47 Primitive.Addresses.material2001
    · exact v2001_mb_checked.trans (by decide +kernel)
    · exact v2001_mg_checked.trans (by decide +kernel)
  upper_error := v2001_upper_checked
  lower_error := reuse_lower_error 23 47 Primitive.Addresses.material2001

def v2002_pa : Scalar.QComplex := ((999999738358186274077243436459 : Int)/10^30,(-723383410782557843512214346 : Int)/10^30)
theorem v2002_pa_checked : Scalar.distance (sourceCoefficient 23 48 1 0) v2002_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2002_pb : Scalar.QComplex := ((-312123673190812609745041 : Int)/10^30,(-431477397565079115570078256 : Int)/10^30)
theorem v2002_pb_checked : Scalar.distance (sourceCoefficient 23 48 1 1) v2002_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2002_pg : Scalar.QComplex := ((-93086404404405442050996 : Int)/10^30,(67337178333764794017 : Int)/10^30)
theorem v2002_pg_checked : Scalar.distance (sourceCoefficient 23 48 1 2) v2002_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2002_mb : Scalar.QComplex := ((-684469118050968903566078 : Int)/10^30,(-431476967557652075589016267 : Int)/10^30)
theorem v2002_mb_checked : Scalar.distance (sourceCoefficient 23 48 3 1) v2002_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2002_mg : Scalar.QComplex := ((-93086311635130675336935 : Int)/10^30,(147666527806034644435 : Int)/10^30)
theorem v2002_mg_checked : Scalar.distance (sourceCoefficient 23 48 3 2) v2002_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2002_upper : Scalar.QComplex := ((999997000481902030217116825312 : Int)/10^30,(-2449291162526567750259182046 : Int)/10^30)
theorem v2002_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 48 5) 1) 14) v2002_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2002 : Material (23 : Basis) (48 : Basis) where
  plus := ![v2002_pa,v2002_pb,v2002_pg]
  minus := ![(Primitive.Addresses.material2002 1).one,v2002_mb,v2002_mg]
  upper := v2002_upper
  lower := (Primitive.Addresses.material2002 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2002_pa_checked.trans (by decide +kernel)
    · exact v2002_pb_checked.trans (by decide +kernel)
    · exact v2002_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 48 Primitive.Addresses.material2002
    · exact v2002_mb_checked.trans (by decide +kernel)
    · exact v2002_mg_checked.trans (by decide +kernel)
  upper_error := v2002_upper_checked
  lower_error := reuse_lower_error 23 48 Primitive.Addresses.material2002

def v2003_pa : Scalar.QComplex := ((999999722173139719314361848769 : Int)/10^30,(-745421788904514772554982560 : Int)/10^30)
theorem v2003_pa_checked : Scalar.distance (sourceCoefficient 23 49 1 0) v2003_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2003_pb : Scalar.QComplex := ((-321632736786677347567748 : Int)/10^30,(-431477389333012425933857699 : Int)/10^30)
theorem v2003_pb_checked : Scalar.distance (sourceCoefficient 23 49 1 1) v2003_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2003_pg : Scalar.QComplex := ((-93086402763113368539054 : Int)/10^30,(69388652148397499544 : Int)/10^30)
theorem v2003_pg_checked : Scalar.distance (sourceCoefficient 23 49 1 2) v2003_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2003_mb : Scalar.QComplex := ((-693978171002271884337484 : Int)/10^30,(-431476951119694840222321254 : Int)/10^30)
theorem v2003_mb_checked : Scalar.distance (sourceCoefficient 23 49 3 1) v2003_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2003_mg : Scalar.QComplex := ((-93086308223509705875767 : Int)/10^30,(149717999440448753400 : Int)/10^30)
theorem v2003_mg_checked : Scalar.distance (sourceCoefficient 23 49 3 2) v2003_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2003_upper : Scalar.QComplex := ((999996946260638248727692087316 : Int)/10^30,(-2471329479891027218828291651 : Int)/10^30)
theorem v2003_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 49 5) 1) 14) v2003_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2003 : Material (23 : Basis) (49 : Basis) where
  plus := ![v2003_pa,v2003_pb,v2003_pg]
  minus := ![(Primitive.Addresses.material2003 1).one,v2003_mb,v2003_mg]
  upper := v2003_upper
  lower := (Primitive.Addresses.material2003 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2003_pa_checked.trans (by decide +kernel)
    · exact v2003_pb_checked.trans (by decide +kernel)
    · exact v2003_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 49 Primitive.Addresses.material2003
    · exact v2003_mb_checked.trans (by decide +kernel)
    · exact v2003_mg_checked.trans (by decide +kernel)
  upper_error := v2003_upper_checked
  lower_error := reuse_lower_error 23 49 Primitive.Addresses.material2003

def v2004_pa : Scalar.QComplex := ((999999720250153039199929371253 : Int)/10^30,(-747997069286787557976504825 : Int)/10^30)
theorem v2004_pa_checked : Scalar.distance (sourceCoefficient 23 50 1 0) v2004_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2004_pb : Scalar.QComplex := ((-322743912238991141036997 : Int)/10^30,(-431477388352826203549667797 : Int)/10^30)
theorem v2004_pb_checked : Scalar.distance (sourceCoefficient 23 50 1 1) v2004_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2004_pg : Scalar.QComplex := ((-93086402567879300945772 : Int)/10^30,(69628375789751284038 : Int)/10^30)
theorem v2004_pg_checked : Scalar.distance (sourceCoefficient 23 50 1 2) v2004_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2004_mb : Scalar.QComplex := ((-695089345194987709714519 : Int)/10^30,(-431476949180614612944051405 : Int)/10^30)
theorem v2004_mb_checked : Scalar.distance (sourceCoefficient 23 50 3 1) v2004_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2004_mg : Scalar.QComplex := ((-93086307821405005240747 : Int)/10^30,(149957722824064262989 : Int)/10^30)
theorem v2004_mg_checked : Scalar.distance (sourceCoefficient 23 50 3 2) v2004_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2004_upper : Scalar.QComplex := ((999996939892954120484483160116 : Int)/10^30,(-2473904753118821830649994445 : Int)/10^30)
theorem v2004_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 50 5) 1) 14) v2004_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2004 : Material (23 : Basis) (50 : Basis) where
  plus := ![v2004_pa,v2004_pb,v2004_pg]
  minus := ![(Primitive.Addresses.material2004 1).one,v2004_mb,v2004_mg]
  upper := v2004_upper
  lower := (Primitive.Addresses.material2004 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2004_pa_checked.trans (by decide +kernel)
    · exact v2004_pb_checked.trans (by decide +kernel)
    · exact v2004_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 50 Primitive.Addresses.material2004
    · exact v2004_mb_checked.trans (by decide +kernel)
    · exact v2004_mg_checked.trans (by decide +kernel)
  upper_error := v2004_upper_checked
  lower_error := reuse_lower_error 23 50 Primitive.Addresses.material2004

def v2005_pa : Scalar.QComplex := ((999999711734510258644080908317 : Int)/10^30,(-759296316589063444114350561 : Int)/10^30)
theorem v2005_pa_checked : Scalar.distance (sourceCoefficient 23 51 1 0) v2005_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2005_pb : Scalar.QComplex := ((-327619282809397971271160 : Int)/10^30,(-431477384007085594272264591 : Int)/10^30)
theorem v2005_pb_checked : Scalar.distance (sourceCoefficient 23 51 1 1) v2005_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2005_pg : Scalar.QComplex := ((-93086401702761540778940 : Int)/10^30,(70680182312094130531 : Int)/10^30)
theorem v2005_pg_checked : Scalar.distance (sourceCoefficient 23 51 1 2) v2005_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2005_mb : Scalar.QComplex := ((-699964710199892840228839 : Int)/10^30,(-431476940627650398062745293 : Int)/10^30)
theorem v2005_mb_checked : Scalar.distance (sourceCoefficient 23 51 3 1) v2005_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2005_mg : Scalar.QComplex := ((-93086306048625910022168 : Int)/10^30,(151009528208213807715 : Int)/10^30)
theorem v2005_mg_checked : Scalar.distance (sourceCoefficient 23 51 3 2) v2005_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2005_upper : Scalar.QComplex := ((999996911875848238957994650929 : Int)/10^30,(-2485203968894969256712931646 : Int)/10^30)
theorem v2005_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 51 5) 1) 14) v2005_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2005 : Material (23 : Basis) (51 : Basis) where
  plus := ![v2005_pa,v2005_pb,v2005_pg]
  minus := ![(Primitive.Addresses.material2005 1).one,v2005_mb,v2005_mg]
  upper := v2005_upper
  lower := (Primitive.Addresses.material2005 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2005_pa_checked.trans (by decide +kernel)
    · exact v2005_pb_checked.trans (by decide +kernel)
    · exact v2005_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 51 Primitive.Addresses.material2005
    · exact v2005_mb_checked.trans (by decide +kernel)
    · exact v2005_mg_checked.trans (by decide +kernel)
  upper_error := v2005_upper_checked
  lower_error := reuse_lower_error 23 51 Primitive.Addresses.material2005

def v2006_pa : Scalar.QComplex := ((999999693075391071444670583536 : Int)/10^30,(-783485241503881228588711378 : Int)/10^30)
theorem v2006_pa_checked : Scalar.distance (sourceCoefficient 23 52 1 0) v2006_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2006_pb : Scalar.QComplex := ((-338056258687681579230116 : Int)/10^30,(-431477374456991508424970761 : Int)/10^30)
theorem v2006_pb_checked : Scalar.distance (sourceCoefficient 23 52 1 1) v2006_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2006_pg : Scalar.QComplex := ((-93086399804143367885123 : Int)/10^30,(72931842815853443579 : Int)/10^30)
theorem v2006_pg_checked : Scalar.distance (sourceCoefficient 23 52 1 2) v2006_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2006_mb : Scalar.QComplex := ((-710401673950712259525817 : Int)/10^30,(-431476922070919749137150886 : Int)/10^30)
theorem v2006_mb_checked : Scalar.distance (sourceCoefficient 23 52 3 1) v2006_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2006_mg : Scalar.QComplex := ((-93086302206926840350917 : Int)/10^30,(153261186235155036625 : Int)/10^30)
theorem v2006_mg_checked : Scalar.distance (sourceCoefficient 23 52 3 2) v2006_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2006_upper : Scalar.QComplex := ((999996851468866841475807115185 : Int)/10^30,(-2509392825579277836249823731 : Int)/10^30)
theorem v2006_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 52 5) 1) 14) v2006_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2006 : Material (23 : Basis) (52 : Basis) where
  plus := ![v2006_pa,v2006_pb,v2006_pg]
  minus := ![(Primitive.Addresses.material2006 1).one,v2006_mb,v2006_mg]
  upper := v2006_upper
  lower := (Primitive.Addresses.material2006 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2006_pa_checked.trans (by decide +kernel)
    · exact v2006_pb_checked.trans (by decide +kernel)
    · exact v2006_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 52 Primitive.Addresses.material2006
    · exact v2006_mb_checked.trans (by decide +kernel)
    · exact v2006_mg_checked.trans (by decide +kernel)
  upper_error := v2006_upper_checked
  lower_error := reuse_lower_error 23 52 Primitive.Addresses.material2006

def v2007_pa : Scalar.QComplex := ((999999690167533244294732796249 : Int)/10^30,(-787187930239820863630859736 : Int)/10^30)
theorem v2007_pa_checked : Scalar.distance (sourceCoefficient 23 53 1 0) v2007_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2007_pb : Scalar.QComplex := ((-339653885405762316303864 : Int)/10^30,(-431477372965416125797487466 : Int)/10^30)
theorem v2007_pb_checked : Scalar.distance (sourceCoefficient 23 53 1 1) v2007_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2007_pg : Scalar.QComplex := ((-93086399507906996456737 : Int)/10^30,(73276512865549124285 : Int)/10^30)
theorem v2007_pg_checked : Scalar.distance (sourceCoefficient 23 53 1 2) v2007_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2007_mb : Scalar.QComplex := ((-711999298786761177164017 : Int)/10^30,(-431476919200665018623982936 : Int)/10^30)
theorem v2007_mb_checked : Scalar.distance (sourceCoefficient 23 53 3 1) v2007_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2007_mg : Scalar.QComplex := ((-93086301613255849700282 : Int)/10^30,(153605855900875659078 : Int)/10^30)
theorem v2007_mg_checked : Scalar.distance (sourceCoefficient 23 53 3 2) v2007_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2007_upper : Scalar.QComplex := ((999996842170508492304888062244 : Int)/10^30,(-2513095503781798736622869164 : Int)/10^30)
theorem v2007_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 53 5) 1) 14) v2007_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2007 : Material (23 : Basis) (53 : Basis) where
  plus := ![v2007_pa,v2007_pb,v2007_pg]
  minus := ![(Primitive.Addresses.material2007 1).one,v2007_mb,v2007_mg]
  upper := v2007_upper
  lower := (Primitive.Addresses.material2007 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2007_pa_checked.trans (by decide +kernel)
    · exact v2007_pb_checked.trans (by decide +kernel)
    · exact v2007_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 53 Primitive.Addresses.material2007
    · exact v2007_mb_checked.trans (by decide +kernel)
    · exact v2007_mg_checked.trans (by decide +kernel)
  upper_error := v2007_upper_checked
  lower_error := reuse_lower_error 23 53 Primitive.Addresses.material2007

def v2008_pa : Scalar.QComplex := ((999999688683903733825051355208 : Int)/10^30,(-789070399656860847119300887 : Int)/10^30)
theorem v2008_pa_checked : Scalar.distance (sourceCoefficient 23 54 1 0) v2008_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2008_pb : Scalar.QComplex := ((-340466128520540353922860 : Int)/10^30,(-431477372204065812170524158 : Int)/10^30)
theorem v2008_pb_checked : Scalar.distance (sourceCoefficient 23 54 1 1) v2008_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2008_pg : Scalar.QComplex := ((-93086399356727718974766 : Int)/10^30,(73451745209741878317 : Int)/10^30)
theorem v2008_pg_checked : Scalar.distance (sourceCoefficient 23 54 1 2) v2008_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2008_mb : Scalar.QComplex := ((-712811540942092951092127 : Int)/10^30,(-431476917738385762500989616 : Int)/10^30)
theorem v2008_mb_checked : Scalar.distance (sourceCoefficient 23 54 3 1) v2008_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2008_mg : Scalar.QComplex := ((-93086301310859007642729 : Int)/10^30,(153781088049360495248 : Int)/10^30)
theorem v2008_mg_checked : Scalar.distance (sourceCoefficient 23 54 3 2) v2008_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2008_upper : Scalar.QComplex := ((999996837437909754007554287711 : Int)/10^30,(-2514977967834511712568673626 : Int)/10^30)
theorem v2008_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 54 5) 1) 14) v2008_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2008 : Material (23 : Basis) (54 : Basis) where
  plus := ![v2008_pa,v2008_pb,v2008_pg]
  minus := ![(Primitive.Addresses.material2008 1).one,v2008_mb,v2008_mg]
  upper := v2008_upper
  lower := (Primitive.Addresses.material2008 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2008_pa_checked.trans (by decide +kernel)
    · exact v2008_pb_checked.trans (by decide +kernel)
    · exact v2008_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 54 Primitive.Addresses.material2008
    · exact v2008_mb_checked.trans (by decide +kernel)
    · exact v2008_mg_checked.trans (by decide +kernel)
  upper_error := v2008_upper_checked
  lower_error := reuse_lower_error 23 54 Primitive.Addresses.material2008

def v2009_pa : Scalar.QComplex := ((999999676459013349638615673783 : Int)/10^30,(-804413990816888220265664936 : Int)/10^30)
theorem v2009_pa_checked : Scalar.distance (sourceCoefficient 23 55 1 0) v2009_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2009_pb : Scalar.QComplex := ((-347086542165550206751543 : Int)/10^30,(-431477365922438922169754287 : Int)/10^30)
theorem v2009_pb_checked : Scalar.distance (sourceCoefficient 23 55 1 1) v2009_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2009_pg : Scalar.QComplex := ((-93086398110146787234433 : Int)/10^30,(74880025221310059195 : Int)/10^30)
theorem v2009_pg_checked : Scalar.distance (sourceCoefficient 23 55 1 2) v2009_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2009_mb : Scalar.QComplex := ((-719431946701259143935111 : Int)/10^30,(-431476905743642408155385315 : Int)/10^30)
theorem v2009_mb_checked : Scalar.distance (sourceCoefficient 23 55 3 1) v2009_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2009_mg : Scalar.QComplex := ((-93086298831737217421886 : Int)/10^30,(155209366453371552027 : Int)/10^30)
theorem v2009_mg_checked : Scalar.distance (sourceCoefficient 23 55 3 2) v2009_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2009_upper : Scalar.QComplex := ((999996798731391194868708391921 : Int)/10^30,(-2530321515043010667969122818 : Int)/10^30)
theorem v2009_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 55 5) 1) 14) v2009_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2009 : Material (23 : Basis) (55 : Basis) where
  plus := ![v2009_pa,v2009_pb,v2009_pg]
  minus := ![(Primitive.Addresses.material2009 1).one,v2009_mb,v2009_mg]
  upper := v2009_upper
  lower := (Primitive.Addresses.material2009 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2009_pa_checked.trans (by decide +kernel)
    · exact v2009_pb_checked.trans (by decide +kernel)
    · exact v2009_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 55 Primitive.Addresses.material2009
    · exact v2009_mb_checked.trans (by decide +kernel)
    · exact v2009_mg_checked.trans (by decide +kernel)
  upper_error := v2009_upper_checked
  lower_error := reuse_lower_error 23 55 Primitive.Addresses.material2009

def v2010_pa : Scalar.QComplex := ((999999673523138694041854232218 : Int)/10^30,(-808055453557969202909644123 : Int)/10^30)
theorem v2010_pa_checked : Scalar.distance (sourceCoefficient 23 56 1 0) v2010_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2010_pb : Scalar.QComplex := ((-348657751228419727645162 : Int)/10^30,(-431477364411747067936362927 : Int)/10^30)
theorem v2010_pb_checked : Scalar.distance (sourceCoefficient 23 56 1 1) v2010_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2010_pg : Scalar.QComplex := ((-93086397810544340482161 : Int)/10^30,(75218995960138670065 : Int)/10^30)
theorem v2010_pg_checked : Scalar.distance (sourceCoefficient 23 56 1 2) v2010_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2010_mb : Scalar.QComplex := ((-721003153875436691752827 : Int)/10^30,(-431476902877068459794501907 : Int)/10^30)
theorem v2010_mb_checked : Scalar.distance (sourceCoefficient 23 56 3 1) v2010_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2010_mg : Scalar.QComplex := ((-93086298239618401291559 : Int)/10^30,(155548336807442447149 : Int)/10^30)
theorem v2010_mg_checked : Scalar.distance (sourceCoefficient 23 56 3 2) v2010_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2010_upper : Scalar.QComplex := ((999996789510686571725909457292 : Int)/10^30,(-2533962967293507338942992174 : Int)/10^30)
theorem v2010_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 56 5) 1) 14) v2010_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2010 : Material (23 : Basis) (56 : Basis) where
  plus := ![v2010_pa,v2010_pb,v2010_pg]
  minus := ![(Primitive.Addresses.material2010 1).one,v2010_mb,v2010_mg]
  upper := v2010_upper
  lower := (Primitive.Addresses.material2010 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2010_pa_checked.trans (by decide +kernel)
    · exact v2010_pb_checked.trans (by decide +kernel)
    · exact v2010_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 56 Primitive.Addresses.material2010
    · exact v2010_mb_checked.trans (by decide +kernel)
    · exact v2010_mg_checked.trans (by decide +kernel)
  upper_error := v2010_upper_checked
  lower_error := reuse_lower_error 23 56 Primitive.Addresses.material2010

def v2011_pa : Scalar.QComplex := ((999999663936618708552224286093 : Int)/10^30,(-819833306010617811120429970 : Int)/10^30)
theorem v2011_pa_checked : Scalar.distance (sourceCoefficient 23 57 1 0) v2011_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2011_pb : Scalar.QComplex := ((-353739628964716536473209 : Int)/10^30,(-431477359473365168092819724 : Int)/10^30)
theorem v2011_pb_checked : Scalar.distance (sourceCoefficient 23 57 1 1) v2011_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2011_pg : Scalar.QComplex := ((-93086396831656660580007 : Int)/10^30,(76315354105909324566 : Int)/10^30)
theorem v2011_pg_checked : Scalar.distance (sourceCoefficient 23 57 1 2) v2011_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2011_mb : Scalar.QComplex := ((-726085025457917002970782 : Int)/10^30,(-431476893553256791588933875 : Int)/10^30)
theorem v2011_mb_checked : Scalar.distance (sourceCoefficient 23 57 3 1) v2011_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2011_mg : Scalar.QComplex := ((-93086296314623384211833 : Int)/10^30,(156644693700252877646 : Int)/10^30)
theorem v2011_mg_checked : Scalar.distance (sourceCoefficient 23 57 3 2) v2011_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2011_upper : Scalar.QComplex := ((999996759596676009388197227997 : Int)/10^30,(-2545740785658964430014402966 : Int)/10^30)
theorem v2011_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 57 5) 1) 14) v2011_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2011 : Material (23 : Basis) (57 : Basis) where
  plus := ![v2011_pa,v2011_pb,v2011_pg]
  minus := ![(Primitive.Addresses.material2011 1).one,v2011_mb,v2011_mg]
  upper := v2011_upper
  lower := (Primitive.Addresses.material2011 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2011_pa_checked.trans (by decide +kernel)
    · exact v2011_pb_checked.trans (by decide +kernel)
    · exact v2011_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 57 Primitive.Addresses.material2011
    · exact v2011_mb_checked.trans (by decide +kernel)
    · exact v2011_mg_checked.trans (by decide +kernel)
  upper_error := v2011_upper_checked
  lower_error := reuse_lower_error 23 57 Primitive.Addresses.material2011

def v2012_pa : Scalar.QComplex := ((999999658677013177323957314876 : Int)/10^30,(-826223854136377952965133320 : Int)/10^30)
theorem v2012_pa_checked : Scalar.distance (sourceCoefficient 23 58 1 0) v2012_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2012_pb : Scalar.QComplex := ((-356497006355818200255868 : Int)/10^30,(-431477356760449086331606790 : Int)/10^30)
theorem v2012_pb_checked : Scalar.distance (sourceCoefficient 23 58 1 1) v2012_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2012_pg : Scalar.QComplex := ((-93086396294217119839079 : Int)/10^30,(76910227365102840310 : Int)/10^30)
theorem v2012_pg_checked : Scalar.distance (sourceCoefficient 23 58 1 2) v2012_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2012_mb : Scalar.QComplex := ((-728842399481196652318752 : Int)/10^30,(-431476888460849219117261026 : Int)/10^30)
theorem v2012_mb_checked : Scalar.distance (sourceCoefficient 23 58 3 1) v2012_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2012_mg : Scalar.QComplex := ((-93086295263835212997229 : Int)/10^30,(157239566274161773660 : Int)/10^30)
theorem v2012_mg_checked : Scalar.distance (sourceCoefficient 23 58 3 2) v2012_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2012_upper : Scalar.QComplex := ((999996743307571992659769289847 : Int)/10^30,(-2552131315189151825841609481 : Int)/10^30)
theorem v2012_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 58 5) 1) 14) v2012_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2012 : Material (23 : Basis) (58 : Basis) where
  plus := ![v2012_pa,v2012_pb,v2012_pg]
  minus := ![(Primitive.Addresses.material2012 1).one,v2012_mb,v2012_mg]
  upper := v2012_upper
  lower := (Primitive.Addresses.material2012 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2012_pa_checked.trans (by decide +kernel)
    · exact v2012_pb_checked.trans (by decide +kernel)
    · exact v2012_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 58 Primitive.Addresses.material2012
    · exact v2012_mb_checked.trans (by decide +kernel)
    · exact v2012_mg_checked.trans (by decide +kernel)
  upper_error := v2012_upper_checked
  lower_error := reuse_lower_error 23 58 Primitive.Addresses.material2012

def v2013_pa : Scalar.QComplex := ((999999644009344408563003968660 : Int)/10^30,(-843789775034947388785521453 : Int)/10^30)
theorem v2013_pa_checked : Scalar.distance (sourceCoefficient 23 59 1 0) v2013_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2013_pb : Scalar.QComplex := ((-364076305006982498669037 : Int)/10^30,(-431477349182313790483348001 : Int)/10^30)
theorem v2013_pb_checked : Scalar.distance (sourceCoefficient 23 59 1 1) v2013_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2013_pg : Scalar.QComplex := ((-93086394794087863835267 : Int)/10^30,(78545376083537622040 : Int)/10^30)
theorem v2013_pg_checked : Scalar.distance (sourceCoefficient 23 59 1 2) v2013_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2013_mb : Scalar.QComplex := ((-736421688770652218069812 : Int)/10^30,(-431476874342123367939730207 : Int)/10^30)
theorem v2013_mb_checked : Scalar.distance (sourceCoefficient 23 59 3 1) v2013_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2013_mg : Scalar.QComplex := ((-93086292352646815915352 : Int)/10^30,(158874713089211972911 : Int)/10^30)
theorem v2013_mg_checked : Scalar.distance (sourceCoefficient 23 59 3 2) v2013_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2013_upper : Scalar.QComplex := ((999996698322739166633264339778 : Int)/10^30,(-2569697184610279866895087165 : Int)/10^30)
theorem v2013_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 59 5) 1) 14) v2013_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2013 : Material (23 : Basis) (59 : Basis) where
  plus := ![v2013_pa,v2013_pb,v2013_pg]
  minus := ![(Primitive.Addresses.material2013 1).one,v2013_mb,v2013_mg]
  upper := v2013_upper
  lower := (Primitive.Addresses.material2013 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2013_pa_checked.trans (by decide +kernel)
    · exact v2013_pb_checked.trans (by decide +kernel)
    · exact v2013_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 59 Primitive.Addresses.material2013
    · exact v2013_mb_checked.trans (by decide +kernel)
    · exact v2013_mg_checked.trans (by decide +kernel)
  upper_error := v2013_upper_checked
  lower_error := reuse_lower_error 23 59 Primitive.Addresses.material2013

def v2014_pa : Scalar.QComplex := ((999999626705533944417388336355 : Int)/10^30,(-864053697846613486504194494 : Int)/10^30)
theorem v2014_pa_checked : Scalar.distance (sourceCoefficient 23 60 1 0) v2014_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2014_pb : Scalar.QComplex := ((-372819730525414124105946 : Int)/10^30,(-431477340219721723248771272 : Int)/10^30)
theorem v2014_pb_checked : Scalar.distance (sourceCoefficient 23 60 1 1) v2014_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2014_pg : Scalar.QComplex := ((-93086393021923597333167 : Int)/10^30,(80431672134494385473 : Int)/10^30)
theorem v2014_pg_checked : Scalar.distance (sourceCoefficient 23 60 1 2) v2014_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2014_mb : Scalar.QComplex := ((-745165103299193634846775 : Int)/10^30,(-431476857834352204748503480 : Int)/10^30)
theorem v2014_mb_checked : Scalar.distance (sourceCoefficient 23 60 3 1) v2014_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2014_mg : Scalar.QComplex := ((-93086288952694672915748 : Int)/10^30,(160761006908516561910 : Int)/10^30)
theorem v2014_mg_checked : Scalar.distance (sourceCoefficient 23 60 3 2) v2014_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2014_upper : Scalar.QComplex := ((999996646045262030262240503019 : Int)/10^30,(-2589961047376406232529721522 : Int)/10^30)
theorem v2014_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 60 5) 1) 14) v2014_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2014 : Material (23 : Basis) (60 : Basis) where
  plus := ![v2014_pa,v2014_pb,v2014_pg]
  minus := ![(Primitive.Addresses.material2014 1).one,v2014_mb,v2014_mg]
  upper := v2014_upper
  lower := (Primitive.Addresses.material2014 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2014_pa_checked.trans (by decide +kernel)
    · exact v2014_pb_checked.trans (by decide +kernel)
    · exact v2014_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 60 Primitive.Addresses.material2014
    · exact v2014_mb_checked.trans (by decide +kernel)
    · exact v2014_mg_checked.trans (by decide +kernel)
  upper_error := v2014_upper_checked
  lower_error := reuse_lower_error 23 60 Primitive.Addresses.material2014

def v2015_pa : Scalar.QComplex := ((999999621625587463897671052954 : Int)/10^30,(-869913031230713657857777588 : Int)/10^30)
theorem v2015_pa_checked : Scalar.distance (sourceCoefficient 23 61 1 0) v2015_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2015_pb : Scalar.QComplex := ((-375347900667227214639619 : Int)/10^30,(-431477337584149935766919162 : Int)/10^30)
theorem v2015_pb_checked : Scalar.distance (sourceCoefficient 23 61 1 1) v2015_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2015_pg : Scalar.QComplex := ((-93086392501189047814198 : Int)/10^30,(80977096506702657402 : Int)/10^30)
theorem v2015_pg_checked : Scalar.distance (sourceCoefficient 23 61 1 2) v2015_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2015_mb : Scalar.QComplex := ((-747693270225273687650064 : Int)/10^30,(-431476853017084430782118545 : Int)/10^30)
theorem v2015_mb_checked : Scalar.distance (sourceCoefficient 23 61 3 1) v2015_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2015_mg : Scalar.QComplex := ((-93086287961283649076141 : Int)/10^30,(161306430628267949718 : Int)/10^30)
theorem v2015_mg_checked : Scalar.distance (sourceCoefficient 23 61 3 2) v2015_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2015_upper : Scalar.QComplex := ((999996630852645249341506884445 : Int)/10^30,(-2595820363266190837682550322 : Int)/10^30)
theorem v2015_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 61 5) 1) 14) v2015_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2015 : Material (23 : Basis) (61 : Basis) where
  plus := ![v2015_pa,v2015_pb,v2015_pg]
  minus := ![(Primitive.Addresses.material2015 1).one,v2015_mb,v2015_mg]
  upper := v2015_upper
  lower := (Primitive.Addresses.material2015 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2015_pa_checked.trans (by decide +kernel)
    · exact v2015_pb_checked.trans (by decide +kernel)
    · exact v2015_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 61 Primitive.Addresses.material2015
    · exact v2015_mb_checked.trans (by decide +kernel)
    · exact v2015_mg_checked.trans (by decide +kernel)
  upper_error := v2015_upper_checked
  lower_error := reuse_lower_error 23 61 Primitive.Addresses.material2015

def v2016_pa : Scalar.QComplex := ((999999614183463176234064931175 : Int)/10^30,(-878426391220762323615444222 : Int)/10^30)
theorem v2016_pa_checked : Scalar.distance (sourceCoefficient 23 62 1 0) v2016_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2016_pb : Scalar.QComplex := ((-379021223385503130417780 : Int)/10^30,(-431477333719580155847874179 : Int)/10^30)
theorem v2016_pb_checked : Scalar.distance (sourceCoefficient 23 62 1 1) v2016_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2016_pg : Scalar.QComplex := ((-93086391737939890911222 : Int)/10^30,(81769574714174858060 : Int)/10^30)
theorem v2016_pg_checked : Scalar.distance (sourceCoefficient 23 62 1 2) v2016_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2016_mb : Scalar.QComplex := ((-751366588240854009964050 : Int)/10^30,(-431476845982604024260704892 : Int)/10^30)
theorem v2016_mb_checked : Scalar.distance (sourceCoefficient 23 62 3 1) v2016_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2016_mg : Scalar.QComplex := ((-93086286514161775210717 : Int)/10^30,(162098907882014648750 : Int)/10^30)
theorem v2016_mg_checked : Scalar.distance (sourceCoefficient 23 62 3 2) v2016_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2016_upper : Scalar.QComplex := ((999996608717245029009034515044 : Int)/10^30,(-2604333697732158471510862558 : Int)/10^30)
theorem v2016_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 23 62 5) 1) 14) v2016_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2016 : Material (23 : Basis) (62 : Basis) where
  plus := ![v2016_pa,v2016_pb,v2016_pg]
  minus := ![(Primitive.Addresses.material2016 1).one,v2016_mb,v2016_mg]
  upper := v2016_upper
  lower := (Primitive.Addresses.material2016 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2016_pa_checked.trans (by decide +kernel)
    · exact v2016_pb_checked.trans (by decide +kernel)
    · exact v2016_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 23 62 Primitive.Addresses.material2016
    · exact v2016_mb_checked.trans (by decide +kernel)
    · exact v2016_mg_checked.trans (by decide +kernel)
  upper_error := v2016_upper_checked
  lower_error := reuse_lower_error 23 62 Primitive.Addresses.material2016

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
