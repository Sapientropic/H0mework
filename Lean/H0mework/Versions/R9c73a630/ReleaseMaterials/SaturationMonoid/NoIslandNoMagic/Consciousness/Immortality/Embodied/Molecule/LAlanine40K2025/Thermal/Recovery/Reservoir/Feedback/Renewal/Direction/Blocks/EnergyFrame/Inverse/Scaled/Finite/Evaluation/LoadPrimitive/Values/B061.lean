import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B040
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B041

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v977_pa : Scalar.QComplex := ((999999769023731944724135587486 : Int)/10^30,(-679670863551259878546898668 : Int)/10^30)
theorem v977_pa_checked : Scalar.distance (sourceCoefficient 10 63 1 0) v977_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v977_pb : Scalar.QComplex := ((-293262669083611873326857 : Int)/10^30,(-431477376880048545041468672 : Int)/10^30)
theorem v977_pb_checked : Scalar.distance (sourceCoefficient 10 63 1 1) v977_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v977_pg : Scalar.QComplex := ((-93086403600396981181758 : Int)/10^30,(63268130933399692715 : Int)/10^30)
theorem v977_pg_checked : Scalar.distance (sourceCoefficient 10 63 1 2) v977_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v977_mb : Scalar.QComplex := ((-665608103116332223556997 : Int)/10^30,(-431476963148826283465625701 : Int)/10^30)
theorem v977_mb_checked : Scalar.distance (sourceCoefficient 10 63 3 1) v977_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v977_mg : Scalar.QComplex := ((-93086314342527157260008 : Int)/10^30,(143597481226938764409 : Int)/10^30)
theorem v977_mg_checked : Scalar.distance (sourceCoefficient 10 63 3 2) v977_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v977_upper : Scalar.QComplex := ((999997106591292978048767831023 : Int)/10^30,(-2405578733325923920776552947 : Int)/10^30)
theorem v977_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 63 5) 1) 14) v977_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material977 : Material (10 : Basis) (63 : Basis) where
  plus := ![v977_pa,v977_pb,v977_pg]
  minus := ![(Primitive.Addresses.material977 1).one,v977_mb,v977_mg]
  upper := v977_upper
  lower := (Primitive.Addresses.material977 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v977_pa_checked.trans (by decide +kernel)
    · exact v977_pb_checked.trans (by decide +kernel)
    · exact v977_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 63 Primitive.Addresses.material977
    · exact v977_mb_checked.trans (by decide +kernel)
    · exact v977_mg_checked.trans (by decide +kernel)
  upper_error := v977_upper_checked
  lower_error := reuse_lower_error 10 63 Primitive.Addresses.material977

def v978_pa : Scalar.QComplex := ((999999744310151098265901885292 : Int)/10^30,(-715108126388009497103134529 : Int)/10^30)
theorem v978_pa_checked : Scalar.distance (sourceCoefficient 10 64 1 0) v978_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v978_pb : Scalar.QComplex := ((-308553046897542710951721 : Int)/10^30,(-431477362118862927397671849 : Int)/10^30)
theorem v978_pb_checked : Scalar.distance (sourceCoefficient 10 64 1 1) v978_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v978_pg : Scalar.QComplex := ((-93086400857867451841037 : Int)/10^30,(66566858730142844000 : Int)/10^30)
theorem v978_pg_checked : Scalar.distance (sourceCoefficient 10 64 1 2) v978_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v978_mb : Scalar.QComplex := ((-680898462498718227362032 : Int)/10^30,(-431476935192738761716277447 : Int)/10^30)
theorem v978_mb_checked : Scalar.distance (sourceCoefficient 10 64 3 1) v978_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v978_mg : Scalar.QComplex := ((-93086308753345129683849 : Int)/10^30,(146896205428735332782 : Int)/10^30)
theorem v978_mg_checked : Scalar.distance (sourceCoefficient 10 64 3 2) v978_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v978_upper : Scalar.QComplex := ((999997020716248126707873831682 : Int)/10^30,(-2441015900729634754858455576 : Int)/10^30)
theorem v978_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 64 5) 1) 14) v978_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material978 : Material (10 : Basis) (64 : Basis) where
  plus := ![v978_pa,v978_pb,v978_pg]
  minus := ![(Primitive.Addresses.material978 1).one,v978_mb,v978_mg]
  upper := v978_upper
  lower := (Primitive.Addresses.material978 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v978_pa_checked.trans (by decide +kernel)
    · exact v978_pb_checked.trans (by decide +kernel)
    · exact v978_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 64 Primitive.Addresses.material978
    · exact v978_mb_checked.trans (by decide +kernel)
    · exact v978_mg_checked.trans (by decide +kernel)
  upper_error := v978_upper_checked
  lower_error := reuse_lower_error 10 64 Primitive.Addresses.material978

def v979_pa : Scalar.QComplex := ((999999717943330996356532361180 : Int)/10^30,(-751074735596480043021924981 : Int)/10^30)
theorem v979_pa_checked : Scalar.distance (sourceCoefficient 10 65 1 0) v979_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v979_pb : Scalar.QComplex := ((-324071825268703772019472 : Int)/10^30,(-431477346398446743991967537 : Int)/10^30)
theorem v979_pb_checked : Scalar.distance (sourceCoefficient 10 65 1 1) v979_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v979_pg : Scalar.QComplex := ((-93086397934919239769325 : Int)/10^30,(69914861436551124546 : Int)/10^30)
theorem v979_pg_checked : Scalar.distance (sourceCoefficient 10 65 1 2) v979_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v979_mb : Scalar.QComplex := ((-696417221525517712620426 : Int)/10^30,(-431476906080321637259951963 : Int)/10^30)
theorem v979_mb_checked : Scalar.distance (sourceCoefficient 10 65 3 1) v979_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v979_mg : Scalar.QComplex := ((-93086302941222458773362 : Int)/10^30,(150244204366156532132 : Int)/10^30)
theorem v979_mg_checked : Scalar.distance (sourceCoefficient 10 65 3 2) v979_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v979_upper : Scalar.QComplex := ((999996932274362666558907061713 : Int)/10^30,(-2476982410863326302802427653 : Int)/10^30)
theorem v979_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 65 5) 1) 14) v979_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material979 : Material (10 : Basis) (65 : Basis) where
  plus := ![v979_pa,v979_pb,v979_pg]
  minus := ![(Primitive.Addresses.material979 1).one,v979_mb,v979_mg]
  upper := v979_upper
  lower := (Primitive.Addresses.material979 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v979_pa_checked.trans (by decide +kernel)
    · exact v979_pb_checked.trans (by decide +kernel)
    · exact v979_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 65 Primitive.Addresses.material979
    · exact v979_mb_checked.trans (by decide +kernel)
    · exact v979_mg_checked.trans (by decide +kernel)
  upper_error := v979_upper_checked
  lower_error := reuse_lower_error 10 65 Primitive.Addresses.material979

def v980_pa : Scalar.QComplex := ((999999704579092918892765966001 : Int)/10^30,(-768662297038629394647095358 : Int)/10^30)
theorem v980_pa_checked : Scalar.distance (sourceCoefficient 10 66 1 0) v980_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v980_pb : Scalar.QComplex := ((-331660460065050572066584 : Int)/10^30,(-431477338440275949067545410 : Int)/10^30)
theorem v980_pb_checked : Scalar.distance (sourceCoefficient 10 66 1 1) v980_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v980_pg : Scalar.QComplex := ((-93086396454461639062305 : Int)/10^30,(71552024459698979899 : Int)/10^30)
theorem v980_pg_checked : Scalar.distance (sourceCoefficient 10 66 1 2) v980_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v980_mb : Scalar.QComplex := ((-704005846628725986931837 : Int)/10^30,(-431476891573503755702713589 : Int)/10^30)
theorem v980_mb_checked : Scalar.distance (sourceCoefficient 10 66 3 1) v980_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v980_mg : Scalar.QComplex := ((-93086300047967455417155 : Int)/10^30,(151881365502145539846 : Int)/10^30)
theorem v980_mg_checked : Scalar.distance (sourceCoefficient 10 66 3 2) v980_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v980_upper : Scalar.QComplex := ((999996888555608975518529198699 : Int)/10^30,(-2494569923045406338945542712 : Int)/10^30)
theorem v980_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 66 5) 1) 14) v980_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material980 : Material (10 : Basis) (66 : Basis) where
  plus := ![v980_pa,v980_pb,v980_pg]
  minus := ![(Primitive.Addresses.material980 1).one,v980_mb,v980_mg]
  upper := v980_upper
  lower := (Primitive.Addresses.material980 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v980_pa_checked.trans (by decide +kernel)
    · exact v980_pb_checked.trans (by decide +kernel)
    · exact v980_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 66 Primitive.Addresses.material980
    · exact v980_mb_checked.trans (by decide +kernel)
    · exact v980_mg_checked.trans (by decide +kernel)
  upper_error := v980_upper_checked
  lower_error := reuse_lower_error 10 66 Primitive.Addresses.material980

def v981_pa : Scalar.QComplex := ((999999681454737668783176799214 : Int)/10^30,(-798179442977172579059585517 : Int)/10^30)
theorem v981_pa_checked : Scalar.distance (sourceCoefficient 10 67 1 0) v981_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v981_pb : Scalar.QComplex := ((-344396440379533343403051 : Int)/10^30,(-431477324684154276426456821 : Int)/10^30)
theorem v981_pb_checked : Scalar.distance (sourceCoefficient 10 67 1 1) v981_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v981_pg : Scalar.QComplex := ((-93086393894315406602540 : Int)/10^30,(74299669695126123968 : Int)/10^30)
theorem v981_pg_checked : Scalar.distance (sourceCoefficient 10 67 1 2) v981_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v981_mb : Scalar.QComplex := ((-716741810330107773363497 : Int)/10^30,(-431476866826809800955839789 : Int)/10^30)
theorem v981_mb_checked : Scalar.distance (sourceCoefficient 10 67 3 1) v981_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v981_mg : Scalar.QComplex := ((-93086295116728087390824 : Int)/10^30,(154629007505207895268 : Int)/10^30)
theorem v981_mg_checked : Scalar.distance (sourceCoefficient 10 67 3 2) v981_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v981_upper : Scalar.QComplex := ((999996814487372051056088877096 : Int)/10^30,(-2524086985111088638858203870 : Int)/10^30)
theorem v981_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 67 5) 1) 14) v981_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material981 : Material (10 : Basis) (67 : Basis) where
  plus := ![v981_pa,v981_pb,v981_pg]
  minus := ![(Primitive.Addresses.material981 1).one,v981_mb,v981_mg]
  upper := v981_upper
  lower := (Primitive.Addresses.material981 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v981_pa_checked.trans (by decide +kernel)
    · exact v981_pb_checked.trans (by decide +kernel)
    · exact v981_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 67 Primitive.Addresses.material981
    · exact v981_mb_checked.trans (by decide +kernel)
    · exact v981_mg_checked.trans (by decide +kernel)
  upper_error := v981_upper_checked
  lower_error := reuse_lower_error 10 67 Primitive.Addresses.material981

def v982_pa : Scalar.QComplex := ((999999641009592878507969875006 : Int)/10^30,(-847337409400099397615119567 : Int)/10^30)
theorem v982_pa_checked : Scalar.distance (sourceCoefficient 10 68 1 0) v982_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v982_pb : Scalar.QComplex := ((-365606989407425606149737 : Int)/10^30,(-431477300662161399079060682 : Int)/10^30)
theorem v982_pb_checked : Scalar.distance (sourceCoefficient 10 68 1 1) v982_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v982_pg : Scalar.QComplex := ((-93086389420630720525019 : Int)/10^30,(78875608377672817665 : Int)/10^30)
theorem v982_pg_checked : Scalar.distance (sourceCoefficient 10 68 1 2) v982_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v982_mb : Scalar.QComplex := ((-737952330730445320293462 : Int)/10^30,(-431476824501077344689499639 : Int)/10^30)
theorem v982_mb_checked : Scalar.distance (sourceCoefficient 10 68 3 1) v982_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v982_mg : Scalar.QComplex := ((-93086286694216076660516 : Int)/10^30,(159204940623335089918 : Int)/10^30)
theorem v982_mg_checked : Scalar.distance (sourceCoefficient 10 68 3 2) v982_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v982_upper : Scalar.QComplex := ((999996689200097028978930717956 : Int)/10^30,(-2573244808514348217695307480 : Int)/10^30)
theorem v982_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 68 5) 1) 14) v982_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material982 : Material (10 : Basis) (68 : Basis) where
  plus := ![v982_pa,v982_pb,v982_pg]
  minus := ![(Primitive.Addresses.material982 1).one,v982_mb,v982_mg]
  upper := v982_upper
  lower := (Primitive.Addresses.material982 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v982_pa_checked.trans (by decide +kernel)
    · exact v982_pb_checked.trans (by decide +kernel)
    · exact v982_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 68 Primitive.Addresses.material982
    · exact v982_mb_checked.trans (by decide +kernel)
    · exact v982_mg_checked.trans (by decide +kernel)
  upper_error := v982_upper_checked
  lower_error := reuse_lower_error 10 68 Primitive.Addresses.material982

def v983_pa : Scalar.QComplex := ((999999622443074539027465778003 : Int)/10^30,(-868972789201545196981423633 : Int)/10^30)
theorem v983_pa_checked : Scalar.distance (sourceCoefficient 10 69 1 0) v983_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v983_pb : Scalar.QComplex := ((-374942165425455717017450 : Int)/10^30,(-431477289649034496945228879 : Int)/10^30)
theorem v983_pb_checked : Scalar.distance (sourceCoefficient 10 69 1 1) v983_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v983_pg : Scalar.QComplex := ((-93086387368506030729543 : Int)/10^30,(80889568208722845316 : Int)/10^30)
theorem v983_pg_checked : Scalar.distance (sourceCoefficient 10 69 1 2) v983_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v983_mb : Scalar.QComplex := ((-747287493768730257309479 : Int)/10^30,(-431476805432118080406511485 : Int)/10^30)
theorem v983_mb_checked : Scalar.distance (sourceCoefficient 10 69 3 1) v983_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v983_mg : Scalar.QComplex := ((-93086282904135522152323 : Int)/10^30,(161218897933604646929 : Int)/10^30)
theorem v983_mg_checked : Scalar.distance (sourceCoefficient 10 69 3 2) v983_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v983_upper : Scalar.QComplex := ((999996633292903551174521408407 : Int)/10^30,(-2594880124048310960491173107 : Int)/10^30)
theorem v983_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 69 5) 1) 14) v983_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material983 : Material (10 : Basis) (69 : Basis) where
  plus := ![v983_pa,v983_pb,v983_pg]
  minus := ![(Primitive.Addresses.material983 1).one,v983_mb,v983_mg]
  upper := v983_upper
  lower := (Primitive.Addresses.material983 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v983_pa_checked.trans (by decide +kernel)
    · exact v983_pb_checked.trans (by decide +kernel)
    · exact v983_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 69 Primitive.Addresses.material983
    · exact v983_mb_checked.trans (by decide +kernel)
    · exact v983_mg_checked.trans (by decide +kernel)
  upper_error := v983_upper_checked
  lower_error := reuse_lower_error 10 69 Primitive.Addresses.material983

def v984_pa : Scalar.QComplex := ((999999609974608813443361687546 : Int)/10^30,(-883204749904181338692525069 : Int)/10^30)
theorem v984_pa_checked : Scalar.distance (sourceCoefficient 10 70 1 0) v984_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v984_pb : Scalar.QComplex := ((-381082933797731296366040 : Int)/10^30,(-431477282257658309645347446 : Int)/10^30)
theorem v984_pb_checked : Scalar.distance (sourceCoefficient 10 70 1 1) v984_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v984_pg : Scalar.QComplex := ((-93086385990880339791725 : Int)/10^30,(82214370324251506767 : Int)/10^30)
theorem v984_pg_checked : Scalar.distance (sourceCoefficient 10 70 1 2) v984_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v984_mb : Scalar.QComplex := ((-753428253476092370267042 : Int)/10^30,(-431476792741538109920690685 : Int)/10^30)
theorem v984_mb_checked : Scalar.distance (sourceCoefficient 10 70 3 1) v984_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v984_mg : Scalar.QComplex := ((-93086280383265785338621 : Int)/10^30,(162543698367020008999 : Int)/10^30)
theorem v984_mg_checked : Scalar.distance (sourceCoefficient 10 70 3 2) v984_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v984_upper : Scalar.QComplex := ((999996596261383336544804948268 : Int)/10^30,(-2609112042034672727184222437 : Int)/10^30)
theorem v984_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 70 5) 1) 14) v984_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material984 : Material (10 : Basis) (70 : Basis) where
  plus := ![v984_pa,v984_pb,v984_pg]
  minus := ![(Primitive.Addresses.material984 1).one,v984_mb,v984_mg]
  upper := v984_upper
  lower := (Primitive.Addresses.material984 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v984_pa_checked.trans (by decide +kernel)
    · exact v984_pb_checked.trans (by decide +kernel)
    · exact v984_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 70 Primitive.Addresses.material984
    · exact v984_mb_checked.trans (by decide +kernel)
    · exact v984_mg_checked.trans (by decide +kernel)
  upper_error := v984_upper_checked
  lower_error := reuse_lower_error 10 70 Primitive.Addresses.material984

def v985_pa : Scalar.QComplex := ((999999588224007535851716694793 : Int)/10^30,(-907497556673751379404359198 : Int)/10^30)
theorem v985_pa_checked : Scalar.distance (sourceCoefficient 10 71 1 0) v985_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v985_pb : Scalar.QComplex := ((-391564728952280073246246 : Int)/10^30,(-431477269371970396298136567 : Int)/10^30)
theorem v985_pb_checked : Scalar.distance (sourceCoefficient 10 71 1 1) v985_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v985_pg : Scalar.QComplex := ((-93086383588566186142659 : Int)/10^30,(84475700451284795247 : Int)/10^30)
theorem v985_pg_checked : Scalar.distance (sourceCoefficient 10 71 1 2) v985_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v985_mb : Scalar.QComplex := ((-763910033608021450026411 : Int)/10^30,(-431476770810537858657634171 : Int)/10^30)
theorem v985_mb_checked : Scalar.distance (sourceCoefficient 10 71 3 1) v985_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v985_mg : Scalar.QComplex := ((-93086276029526473079378 : Int)/10^30,(164805025578967824907 : Int)/10^30)
theorem v985_mg_checked : Scalar.distance (sourceCoefficient 10 71 3 2) v985_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v985_upper : Scalar.QComplex := ((999996532583633795855657308887 : Int)/10^30,(-2633404775083396112172395697 : Int)/10^30)
theorem v985_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 71 5) 1) 14) v985_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material985 : Material (10 : Basis) (71 : Basis) where
  plus := ![v985_pa,v985_pb,v985_pg]
  minus := ![(Primitive.Addresses.material985 1).one,v985_mb,v985_mg]
  upper := v985_upper
  lower := (Primitive.Addresses.material985 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v985_pa_checked.trans (by decide +kernel)
    · exact v985_pb_checked.trans (by decide +kernel)
    · exact v985_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 71 Primitive.Addresses.material985
    · exact v985_mb_checked.trans (by decide +kernel)
    · exact v985_mg_checked.trans (by decide +kernel)
  upper_error := v985_upper_checked
  lower_error := reuse_lower_error 10 71 Primitive.Addresses.material985

def v986_pa : Scalar.QComplex := ((999999563952494813464703738416 : Int)/10^30,(-933860171672206937750308713 : Int)/10^30)
theorem v986_pa_checked : Scalar.distance (sourceCoefficient 10 72 1 0) v986_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v986_pb : Scalar.QComplex := ((-402939599131734513220029 : Int)/10^30,(-431477255004256484849326350 : Int)/10^30)
theorem v986_pb_checked : Scalar.distance (sourceCoefficient 10 72 1 1) v986_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v986_pg : Scalar.QComplex := ((-93086380909055474134045 : Int)/10^30,(86929701561554484106 : Int)/10^30)
theorem v986_pg_checked : Scalar.distance (sourceCoefficient 10 72 1 2) v986_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v986_mb : Scalar.QComplex := ((-775284887153401857173484 : Int)/10^30,(-431476746626828637231390530 : Int)/10^30)
theorem v986_mb_checked : Scalar.distance (sourceCoefficient 10 72 3 1) v986_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v986_mg : Scalar.QComplex := ((-93086271232324324719479 : Int)/10^30,(167259023463203683240 : Int)/10^30)
theorem v986_mg_checked : Scalar.distance (sourceCoefficient 10 72 3 2) v986_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v986_upper : Scalar.QComplex := ((999996462812675333451941984127 : Int)/10^30,(-2659767308927404336206693239 : Int)/10^30)
theorem v986_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 72 5) 1) 14) v986_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material986 : Material (10 : Basis) (72 : Basis) where
  plus := ![v986_pa,v986_pb,v986_pg]
  minus := ![(Primitive.Addresses.material986 1).one,v986_mb,v986_mg]
  upper := v986_upper
  lower := (Primitive.Addresses.material986 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v986_pa_checked.trans (by decide +kernel)
    · exact v986_pb_checked.trans (by decide +kernel)
    · exact v986_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 72 Primitive.Addresses.material986
    · exact v986_mb_checked.trans (by decide +kernel)
    · exact v986_mg_checked.trans (by decide +kernel)
  upper_error := v986_upper_checked
  lower_error := reuse_lower_error 10 72 Primitive.Addresses.material986

def v987_pa : Scalar.QComplex := ((999999555083202071239906405831 : Int)/10^30,(-943309810140106148152729140 : Int)/10^30)
theorem v987_pa_checked : Scalar.distance (sourceCoefficient 10 73 1 0) v987_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v987_pb : Scalar.QComplex := ((-407016903636544755763051 : Int)/10^30,(-431477249756826626698482433 : Int)/10^30)
theorem v987_pb_checked : Scalar.distance (sourceCoefficient 10 73 1 1) v987_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v987_pg : Scalar.QComplex := ((-93086379930213038387890 : Int)/10^30,(87809334446446958807 : Int)/10^30)
theorem v987_pg_checked : Scalar.distance (sourceCoefficient 10 73 1 2) v987_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v987_mb : Scalar.QComplex := ((-779362185611749658437748 : Int)/10^30,(-431476737860870580265308718 : Int)/10^30)
theorem v987_mb_checked : Scalar.distance (sourceCoefficient 10 73 3 1) v987_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v987_mg : Scalar.QComplex := ((-93086269494398690973369 : Int)/10^30,(168138655175871697065 : Int)/10^30)
theorem v987_mg_checked : Scalar.distance (sourceCoefficient 10 73 3 2) v987_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v987_upper : Scalar.QComplex := ((999996437634177069908011727845 : Int)/10^30,(-2669216918013582424055469682 : Int)/10^30)
theorem v987_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 73 5) 1) 14) v987_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material987 : Material (10 : Basis) (73 : Basis) where
  plus := ![v987_pa,v987_pb,v987_pg]
  minus := ![(Primitive.Addresses.material987 1).one,v987_mb,v987_mg]
  upper := v987_upper
  lower := (Primitive.Addresses.material987 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v987_pa_checked.trans (by decide +kernel)
    · exact v987_pb_checked.trans (by decide +kernel)
    · exact v987_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 73 Primitive.Addresses.material987
    · exact v987_mb_checked.trans (by decide +kernel)
    · exact v987_mg_checked.trans (by decide +kernel)
  upper_error := v987_upper_checked
  lower_error := reuse_lower_error 10 73 Primitive.Addresses.material987

def v988_pa : Scalar.QComplex := ((999999544996295664774661641833 : Int)/10^30,(-953942976095573397214280683 : Int)/10^30)
theorem v988_pa_checked : Scalar.distance (sourceCoefficient 10 74 1 0) v988_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v988_pb : Scalar.QComplex := ((-411604873341007294928330 : Int)/10^30,(-431477243790751970827485375 : Int)/10^30)
theorem v988_pb_checked : Scalar.distance (sourceCoefficient 10 74 1 1) v988_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v988_pg : Scalar.QComplex := ((-93086378817179174897135 : Int)/10^30,(88799137646756414532 : Int)/10^30)
theorem v988_pg_checked : Scalar.distance (sourceCoefficient 10 74 1 2) v988_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v988_mb : Scalar.QComplex := ((-783950148459447670068841 : Int)/10^30,(-431476727935586925370254177 : Int)/10^30)
theorem v988_mb_checked : Scalar.distance (sourceCoefficient 10 74 3 1) v988_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v988_mg : Scalar.QComplex := ((-93086267527209659130218 : Int)/10^30,(169128457047134090066 : Int)/10^30)
theorem v988_mg_checked : Scalar.distance (sourceCoefficient 10 74 3 2) v988_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v988_upper : Scalar.QComplex := ((999996409195405880848674582330 : Int)/10^30,(-2679850050723112661305314073 : Int)/10^30)
theorem v988_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 74 5) 1) 14) v988_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material988 : Material (10 : Basis) (74 : Basis) where
  plus := ![v988_pa,v988_pb,v988_pg]
  minus := ![(Primitive.Addresses.material988 1).one,v988_mb,v988_mg]
  upper := v988_upper
  lower := (Primitive.Addresses.material988 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v988_pa_checked.trans (by decide +kernel)
    · exact v988_pb_checked.trans (by decide +kernel)
    · exact v988_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 74 Primitive.Addresses.material988
    · exact v988_mb_checked.trans (by decide +kernel)
    · exact v988_mg_checked.trans (by decide +kernel)
  upper_error := v988_upper_checked
  lower_error := reuse_lower_error 10 74 Primitive.Addresses.material988

def v989_pa : Scalar.QComplex := ((999999530753763498970492626610 : Int)/10^30,(-968758098190682762339242961 : Int)/10^30)
theorem v989_pa_checked : Scalar.distance (sourceCoefficient 10 75 1 0) v989_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v989_pb : Scalar.QComplex := ((-417997262093070862177325 : Int)/10^30,(-431477235369807960193757557 : Int)/10^30)
theorem v989_pb_checked : Scalar.distance (sourceCoefficient 10 75 1 1) v989_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v989_pg : Scalar.QComplex := ((-93086377245923878019137 : Int)/10^30,(90178224104013937027 : Int)/10^30)
theorem v989_pg_checked : Scalar.distance (sourceCoefficient 10 75 1 2) v989_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v989_mb : Scalar.QComplex := ((-790342527564437342388610 : Int)/10^30,(-431476713998302459709928839 : Int)/10^30)
theorem v989_mb_checked : Scalar.distance (sourceCoefficient 10 75 3 1) v989_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v989_mg : Scalar.QComplex := ((-93086264765865446437473 : Int)/10^30,(170507541634972142664 : Int)/10^30)
theorem v989_mg_checked : Scalar.distance (sourceCoefficient 10 75 3 2) v989_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v989_upper : Scalar.QComplex := ((999996369383338208841937703515 : Int)/10^30,(-2694665126171519526503002002 : Int)/10^30)
theorem v989_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 75 5) 1) 14) v989_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material989 : Material (10 : Basis) (75 : Basis) where
  plus := ![v989_pa,v989_pb,v989_pg]
  minus := ![(Primitive.Addresses.material989 1).one,v989_mb,v989_mg]
  upper := v989_upper
  lower := (Primitive.Addresses.material989 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v989_pa_checked.trans (by decide +kernel)
    · exact v989_pb_checked.trans (by decide +kernel)
    · exact v989_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 75 Primitive.Addresses.material989
    · exact v989_mb_checked.trans (by decide +kernel)
    · exact v989_mg_checked.trans (by decide +kernel)
  upper_error := v989_upper_checked
  lower_error := reuse_lower_error 10 75 Primitive.Addresses.material989

def v990_pa : Scalar.QComplex := ((999999518634666436350032959562 : Int)/10^30,(-981188277250964498719696305 : Int)/10^30)
theorem v990_pa_checked : Scalar.distance (sourceCoefficient 10 76 1 0) v990_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v990_pb : Scalar.QComplex := ((-423360602008616854242860 : Int)/10^30,(-431477228207052849217238400 : Int)/10^30)
theorem v990_pb_checked : Scalar.distance (sourceCoefficient 10 76 1 1) v990_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v990_pg : Scalar.QComplex := ((-93086375909220141593931 : Int)/10^30,(91335304779552846159 : Int)/10^30)
theorem v990_pg_checked : Scalar.distance (sourceCoefficient 10 76 1 2) v990_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v990_mb : Scalar.QComplex := ((-795705859301831704895262 : Int)/10^30,(-431476702207229224501121493 : Int)/10^30)
theorem v990_mb_checked : Scalar.distance (sourceCoefficient 10 76 3 1) v990_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v990_mg : Scalar.QComplex := ((-93086262430653697717182 : Int)/10^30,(171664620726161913461 : Int)/10^30)
theorem v990_mg_checked : Scalar.distance (sourceCoefficient 10 76 3 2) v990_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v990_upper : Scalar.QComplex := ((999996335810897795182242081435 : Int)/10^30,(-2707095265802047609810557028 : Int)/10^30)
theorem v990_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 76 5) 1) 14) v990_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material990 : Material (10 : Basis) (76 : Basis) where
  plus := ![v990_pa,v990_pb,v990_pg]
  minus := ![(Primitive.Addresses.material990 1).one,v990_mb,v990_mg]
  upper := v990_upper
  lower := (Primitive.Addresses.material990 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v990_pa_checked.trans (by decide +kernel)
    · exact v990_pb_checked.trans (by decide +kernel)
    · exact v990_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 76 Primitive.Addresses.material990
    · exact v990_mb_checked.trans (by decide +kernel)
    · exact v990_mg_checked.trans (by decide +kernel)
  upper_error := v990_upper_checked
  lower_error := reuse_lower_error 10 76 Primitive.Addresses.material990

def v991_pa : Scalar.QComplex := ((999999515806966817627804809671 : Int)/10^30,(-984065969293650052514236237 : Int)/10^30)
theorem v991_pa_checked : Scalar.distance (sourceCoefficient 10 77 1 0) v991_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v991_pb : Scalar.QComplex := ((-424602260748881662500438 : Int)/10^30,(-431477226536142745299927357 : Int)/10^30)
theorem v991_pb_checked : Scalar.distance (sourceCoefficient 10 77 1 1) v991_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v991_pg : Scalar.QComplex := ((-93086375597369863207194 : Int)/10^30,(91603178783879531885 : Int)/10^30)
theorem v991_pg_checked : Scalar.distance (sourceCoefficient 10 77 1 2) v991_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v991_mb : Scalar.QComplex := ((-796947516137850052861327 : Int)/10^30,(-431476699464824172125207607 : Int)/10^30)
theorem v991_mb_checked : Scalar.distance (sourceCoefficient 10 77 3 1) v991_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v991_mg : Scalar.QComplex := ((-93086261887640334309922 : Int)/10^30,(171932494361634119896 : Int)/10^30)
theorem v991_mg_checked : Scalar.distance (sourceCoefficient 10 77 3 2) v991_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v991_upper : Scalar.QComplex := ((999996328016566984493971813578 : Int)/10^30,(-2709972948678395888469100857 : Int)/10^30)
theorem v991_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 77 5) 1) 14) v991_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material991 : Material (10 : Basis) (77 : Basis) where
  plus := ![v991_pa,v991_pb,v991_pg]
  minus := ![(Primitive.Addresses.material991 1).one,v991_mb,v991_mg]
  upper := v991_upper
  lower := (Primitive.Addresses.material991 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v991_pa_checked.trans (by decide +kernel)
    · exact v991_pb_checked.trans (by decide +kernel)
    · exact v991_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 77 Primitive.Addresses.material991
    · exact v991_mb_checked.trans (by decide +kernel)
    · exact v991_mg_checked.trans (by decide +kernel)
  upper_error := v991_upper_checked
  lower_error := reuse_lower_error 10 77 Primitive.Addresses.material991

def v992_pa : Scalar.QComplex := ((999999498633391930247312712993 : Int)/10^30,(-1001365550022083437564097175 : Int)/10^30)
theorem v992_pa_checked : Scalar.distance (sourceCoefficient 10 78 1 0) v992_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v992_pb : Scalar.QComplex := ((-432066636737020003526408 : Int)/10^30,(-431477216390864836934118340 : Int)/10^30)
theorem v992_pb_checked : Scalar.distance (sourceCoefficient 10 78 1 1) v992_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v992_pg : Scalar.QComplex := ((-93086373703691575273444 : Int)/10^30,(93213534537511955691 : Int)/10^30)
theorem v992_pg_checked : Scalar.distance (sourceCoefficient 10 78 1 2) v992_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v992_mb : Scalar.QComplex := ((-804411880591742166103530 : Int)/10^30,(-431476682878129746561443303 : Int)/10^30)
theorem v992_mb_checked : Scalar.distance (sourceCoefficient 10 78 3 1) v992_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v992_mg : Scalar.QComplex := ((-93086258604298263825149 : Int)/10^30,(173542847881498425348 : Int)/10^30)
theorem v992_mg_checked : Scalar.distance (sourceCoefficient 10 78 3 2) v992_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v992_upper : Scalar.QComplex := ((999996280985510743564060955504 : Int)/10^30,(-2727272474001103648945478354 : Int)/10^30)
theorem v992_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 78 5) 1) 14) v992_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material992 : Material (10 : Basis) (78 : Basis) where
  plus := ![v992_pa,v992_pb,v992_pg]
  minus := ![(Primitive.Addresses.material992 1).one,v992_mb,v992_mg]
  upper := v992_upper
  lower := (Primitive.Addresses.material992 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v992_pa_checked.trans (by decide +kernel)
    · exact v992_pb_checked.trans (by decide +kernel)
    · exact v992_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 78 Primitive.Addresses.material992
    · exact v992_mb_checked.trans (by decide +kernel)
    · exact v992_mg_checked.trans (by decide +kernel)
  upper_error := v992_upper_checked
  lower_error := reuse_lower_error 10 78 Primitive.Addresses.material992

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
