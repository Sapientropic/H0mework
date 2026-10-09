import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B086

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2065_pa : Scalar.QComplex := ((999999795245336661782673485095 : Int)/10^30,(-639929124788020954069058416 : Int)/10^30)
theorem v2065_pa_checked : Scalar.distance (sourceCoefficient 24 38 1 0) v2065_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2065_pb : Scalar.QComplex := ((-276115030583743047336267 : Int)/10^30,(-431477429847199237040699906 : Int)/10^30)
theorem v2065_pb_checked : Scalar.distance (sourceCoefficient 24 38 1 1) v2065_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2065_pg : Scalar.QComplex := ((-93086410534368757906045 : Int)/10^30,(59568717419889693979 : Int)/10^30)
theorem v2065_pg_checked : Scalar.distance (sourceCoefficient 24 38 1 2) v2065_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2065_mb : Scalar.QComplex := ((-648460516709578392145896 : Int)/10^30,(-431477030913596977791858239 : Int)/10^30)
theorem v2065_mb_checked : Scalar.distance (sourceCoefficient 24 38 3 1) v2065_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2065_mg : Scalar.QComplex := ((-93086324468923598909240 : Int)/10^30,(139898075074594837119 : Int)/10^30)
theorem v2065_mg_checked : Scalar.distance (sourceCoefficient 24 38 3 2) v2065_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2065_upper : Scalar.QComplex := ((999997201403494404080457435501 : Int)/10^30,(-2365837099009447427816581510 : Int)/10^30)
theorem v2065_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 38 5) 1) 14) v2065_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2065 : Material (24 : Basis) (38 : Basis) where
  plus := ![v2065_pa,v2065_pb,v2065_pg]
  minus := ![(Primitive.Addresses.material2065 1).one,v2065_mb,v2065_mg]
  upper := v2065_upper
  lower := (Primitive.Addresses.material2065 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2065_pa_checked.trans (by decide +kernel)
    · exact v2065_pb_checked.trans (by decide +kernel)
    · exact v2065_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 38 Primitive.Addresses.material2065
    · exact v2065_mb_checked.trans (by decide +kernel)
    · exact v2065_mg_checked.trans (by decide +kernel)
  upper_error := v2065_upper_checked
  lower_error := reuse_lower_error 24 38 Primitive.Addresses.material2065

def v2066_pa : Scalar.QComplex := ((999999786503802799667576980311 : Int)/10^30,(-653446515653759245780617762 : Int)/10^30)
theorem v2066_pa_checked : Scalar.distance (sourceCoefficient 24 39 1 0) v2066_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2066_pb : Scalar.QComplex := ((-281947480587402195415652 : Int)/10^30,(-431477425678220846289124963 : Int)/10^30)
theorem v2066_pb_checked : Scalar.distance (sourceCoefficient 24 39 1 1) v2066_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2066_pg : Scalar.QComplex := ((-93086409677804532503876 : Int)/10^30,(60827003045013582803 : Int)/10^30)
theorem v2066_pg_checked : Scalar.distance (sourceCoefficient 24 39 1 2) v2066_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2066_mb : Scalar.QComplex := ((-654292960943909260327663 : Int)/10^30,(-431477021711478469980509011 : Int)/10^30)
theorem v2066_mb_checked : Scalar.distance (sourceCoefficient 24 39 3 1) v2066_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2066_mg : Scalar.QComplex := ((-93086322526515869043989 : Int)/10^30,(141156359492025132914 : Int)/10^30)
theorem v2066_mg_checked : Scalar.distance (sourceCoefficient 24 39 3 2) v2066_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2066_upper : Scalar.QComplex := ((999997169332183215309007033792 : Int)/10^30,(-2379354454655525469029963738 : Int)/10^30)
theorem v2066_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 39 5) 1) 14) v2066_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2066 : Material (24 : Basis) (39 : Basis) where
  plus := ![v2066_pa,v2066_pb,v2066_pg]
  minus := ![(Primitive.Addresses.material2066 1).one,v2066_mb,v2066_mg]
  upper := v2066_upper
  lower := (Primitive.Addresses.material2066 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2066_pa_checked.trans (by decide +kernel)
    · exact v2066_pb_checked.trans (by decide +kernel)
    · exact v2066_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 39 Primitive.Addresses.material2066
    · exact v2066_mb_checked.trans (by decide +kernel)
    · exact v2066_mg_checked.trans (by decide +kernel)
  upper_error := v2066_upper_checked
  lower_error := reuse_lower_error 24 39 Primitive.Addresses.material2066

def v2067_pa : Scalar.QComplex := ((999999771388919033400566621472 : Int)/10^30,(-676182009277215631274748237 : Int)/10^30)
theorem v2067_pa_checked : Scalar.distance (sourceCoefficient 24 40 1 0) v2067_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2067_pb : Scalar.QComplex := ((-291757334450123059692197 : Int)/10^30,(-431477418429142450291443418 : Int)/10^30)
theorem v2067_pb_checked : Scalar.distance (sourceCoefficient 24 40 1 1) v2067_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2067_pg : Scalar.QComplex := ((-93086408192355618693954 : Int)/10^30,(62943368917457696001 : Int)/10^30)
theorem v2067_pg_checked : Scalar.distance (sourceCoefficient 24 40 1 2) v2067_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2067_mb : Scalar.QComplex := ((-664102804898345029668843 : Int)/10^30,(-431477005996940709034776926 : Int)/10^30)
theorem v2067_mb_checked : Scalar.distance (sourceCoefficient 24 40 3 1) v2067_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2067_mg : Scalar.QComplex := ((-93086319214739077995855 : Int)/10^30,(143272723294573998620 : Int)/10^30)
theorem v2067_mg_checked : Scalar.distance (sourceCoefficient 24 40 3 2) v2067_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2067_upper : Scalar.QComplex := ((999997114977922514669906387133 : Int)/10^30,(-2402089888330216632040268767 : Int)/10^30)
theorem v2067_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 40 5) 1) 14) v2067_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2067 : Material (24 : Basis) (40 : Basis) where
  plus := ![v2067_pa,v2067_pb,v2067_pg]
  minus := ![(Primitive.Addresses.material2067 1).one,v2067_mb,v2067_mg]
  upper := v2067_upper
  lower := (Primitive.Addresses.material2067 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2067_pa_checked.trans (by decide +kernel)
    · exact v2067_pb_checked.trans (by decide +kernel)
    · exact v2067_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 40 Primitive.Addresses.material2067
    · exact v2067_mb_checked.trans (by decide +kernel)
    · exact v2067_mg_checked.trans (by decide +kernel)
  upper_error := v2067_upper_checked
  lower_error := reuse_lower_error 24 40 Primitive.Addresses.material2067

def v2068_pa : Scalar.QComplex := ((999999761490209604261158808220 : Int)/10^30,(-690666000252334390067420934 : Int)/10^30)
theorem v2068_pa_checked : Scalar.distance (sourceCoefficient 24 41 1 0) v2068_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2068_pb : Scalar.QComplex := ((-298006850566520035022856 : Int)/10^30,(-431477413655937862737063416 : Int)/10^30)
theorem v2068_pb_checked : Scalar.distance (sourceCoefficient 24 41 1 1) v2068_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2068_pg : Scalar.QComplex := ((-93086407216755213789077 : Int)/10^30,(64291631884440003233 : Int)/10^30)
theorem v2068_pg_checked : Scalar.distance (sourceCoefficient 24 41 1 2) v2068_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2068_mb : Scalar.QComplex := ((-670352314568700955963490 : Int)/10^30,(-431476995830686958069329616 : Int)/10^30)
theorem v2068_mb_checked : Scalar.distance (sourceCoefficient 24 41 3 1) v2068_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2068_mg : Scalar.QComplex := ((-93086317075648819355736 : Int)/10^30,(144620984917637174562 : Int)/10^30)
theorem v2068_mg_checked : Scalar.distance (sourceCoefficient 24 41 3 2) v2068_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2068_upper : Scalar.QComplex := ((999997080081173382837466142692 : Int)/10^30,(-2416573840648857771700930225 : Int)/10^30)
theorem v2068_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 41 5) 1) 14) v2068_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2068 : Material (24 : Basis) (41 : Basis) where
  plus := ![v2068_pa,v2068_pb,v2068_pg]
  minus := ![(Primitive.Addresses.material2068 1).one,v2068_mb,v2068_mg]
  upper := v2068_upper
  lower := (Primitive.Addresses.material2068 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2068_pa_checked.trans (by decide +kernel)
    · exact v2068_pb_checked.trans (by decide +kernel)
    · exact v2068_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 41 Primitive.Addresses.material2068
    · exact v2068_mb_checked.trans (by decide +kernel)
    · exact v2068_mg_checked.trans (by decide +kernel)
  upper_error := v2068_upper_checked
  lower_error := reuse_lower_error 24 41 Primitive.Addresses.material2068

def v2069_pa : Scalar.QComplex := ((999999753352456006985819732249 : Int)/10^30,(-702349647363061899294884536 : Int)/10^30)
theorem v2069_pa_checked : Scalar.distance (sourceCoefficient 24 42 1 0) v2069_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2069_pb : Scalar.QComplex := ((-303048081306378795120017 : Int)/10^30,(-431477409717642844108228791 : Int)/10^30)
theorem v2069_pb_checked : Scalar.distance (sourceCoefficient 24 42 1 1) v2069_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2069_pg : Scalar.QComplex := ((-93086406413176536568487 : Int)/10^30,(65379220844213453521 : Int)/10^30)
theorem v2069_pg_checked : Scalar.distance (sourceCoefficient 24 42 1 2) v2069_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2069_mb : Scalar.QComplex := ((-675393540032907889131162 : Int)/10^30,(-431476987542038325953692309 : Int)/10^30)
theorem v2069_mb_checked : Scalar.distance (sourceCoefficient 24 42 3 1) v2069_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2069_mg : Scalar.QComplex := ((-93086315333530152248132 : Int)/10^30,(145708572778999343253 : Int)/10^30)
theorem v2069_mg_checked : Scalar.distance (sourceCoefficient 24 42 3 2) v2069_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2069_upper : Scalar.QComplex := ((999997051778516924860650933964 : Int)/10^30,(-2428257456313140909441490283 : Int)/10^30)
theorem v2069_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 42 5) 1) 14) v2069_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2069 : Material (24 : Basis) (42 : Basis) where
  plus := ![v2069_pa,v2069_pb,v2069_pg]
  minus := ![(Primitive.Addresses.material2069 1).one,v2069_mb,v2069_mg]
  upper := v2069_upper
  lower := (Primitive.Addresses.material2069 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2069_pa_checked.trans (by decide +kernel)
    · exact v2069_pb_checked.trans (by decide +kernel)
    · exact v2069_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 42 Primitive.Addresses.material2069
    · exact v2069_mb_checked.trans (by decide +kernel)
    · exact v2069_mg_checked.trans (by decide +kernel)
  upper_error := v2069_upper_checked
  lower_error := reuse_lower_error 24 42 Primitive.Addresses.material2069

def v2070_pa : Scalar.QComplex := ((999999742361855775983346637057 : Int)/10^30,(-717827431957444732711796152 : Int)/10^30)
theorem v2070_pa_checked : Scalar.distance (sourceCoefficient 24 43 1 0) v2070_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2070_pb : Scalar.QComplex := ((-309726396930735107681624 : Int)/10^30,(-431477404379500812290012310 : Int)/10^30)
theorem v2070_pb_checked : Scalar.distance (sourceCoefficient 24 43 1 1) v2070_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2070_pg : Scalar.QComplex := ((-93086405325816568588549 : Int)/10^30,(66819992500559578780 : Int)/10^30)
theorem v2070_pg_checked : Scalar.distance (sourceCoefficient 24 43 1 2) v2070_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2070_mb : Scalar.QComplex := ((-682071848564045928176144 : Int)/10^30,(-431476976440812678120457927 : Int)/10^30)
theorem v2070_mb_checked : Scalar.distance (sourceCoefficient 24 43 3 1) v2070_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2070_mg : Scalar.QComplex := ((-93086313002849539661872 : Int)/10^30,(147149342960537654846 : Int)/10^30)
theorem v2070_mg_checked : Scalar.distance (sourceCoefficient 24 43 3 2) v2070_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2070_upper : Scalar.QComplex := ((999997014074680986811317115782 : Int)/10^30,(-2443735198886402798575666500 : Int)/10^30)
theorem v2070_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 43 5) 1) 14) v2070_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2070 : Material (24 : Basis) (43 : Basis) where
  plus := ![v2070_pa,v2070_pb,v2070_pg]
  minus := ![(Primitive.Addresses.material2070 1).one,v2070_mb,v2070_mg]
  upper := v2070_upper
  lower := (Primitive.Addresses.material2070 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2070_pa_checked.trans (by decide +kernel)
    · exact v2070_pb_checked.trans (by decide +kernel)
    · exact v2070_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 43 Primitive.Addresses.material2070
    · exact v2070_mb_checked.trans (by decide +kernel)
    · exact v2070_mg_checked.trans (by decide +kernel)
  upper_error := v2070_upper_checked
  lower_error := reuse_lower_error 24 43 Primitive.Addresses.material2070

def v2071_pa : Scalar.QComplex := ((999999738141271596994884637529 : Int)/10^30,(-723683209861895711154519877 : Int)/10^30)
theorem v2071_pa_checked : Scalar.distance (sourceCoefficient 24 44 1 0) v2071_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2071_pb : Scalar.QComplex := ((-312253033262860650465968 : Int)/10^30,(-431477402323963409449370445 : Int)/10^30)
theorem v2071_pb_checked : Scalar.distance (sourceCoefficient 24 44 1 1) v2071_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2071_pg : Scalar.QComplex := ((-93086404907647456062327 : Int)/10^30,(67365085938206175338 : Int)/10^30)
theorem v2071_pg_checked : Scalar.distance (sourceCoefficient 24 44 1 2) v2071_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2071_mb : Scalar.QComplex := ((-684598482181553090841783 : Int)/10^30,(-431476972204902681502102715 : Int)/10^30)
theorem v2071_mb_checked : Scalar.distance (sourceCoefficient 24 44 3 1) v2071_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2071_mg : Scalar.QComplex := ((-93086312114289496247198 : Int)/10^30,(147694435834359942095 : Int)/10^30)
theorem v2071_mg_checked : Scalar.distance (sourceCoefficient 24 44 3 2) v2071_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2071_upper : Scalar.QComplex := ((999996999747561662826551253740 : Int)/10^30,(-2449590960785015051803078023 : Int)/10^30)
theorem v2071_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 44 5) 1) 14) v2071_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2071 : Material (24 : Basis) (44 : Basis) where
  plus := ![v2071_pa,v2071_pb,v2071_pg]
  minus := ![(Primitive.Addresses.material2071 1).one,v2071_mb,v2071_mg]
  upper := v2071_upper
  lower := (Primitive.Addresses.material2071 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2071_pa_checked.trans (by decide +kernel)
    · exact v2071_pb_checked.trans (by decide +kernel)
    · exact v2071_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 44 Primitive.Addresses.material2071
    · exact v2071_mb_checked.trans (by decide +kernel)
    · exact v2071_mg_checked.trans (by decide +kernel)
  upper_error := v2071_upper_checked
  lower_error := reuse_lower_error 24 44 Primitive.Addresses.material2071

def v2072_pa : Scalar.QComplex := ((999999736028704611690696006814 : Int)/10^30,(-726596532537675835421708226 : Int)/10^30)
theorem v2072_pa_checked : Scalar.distance (sourceCoefficient 24 45 1 0) v2072_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2072_pb : Scalar.QComplex := ((-313510066406216358743900 : Int)/10^30,(-431477401293959162488513895 : Int)/10^30)
theorem v2072_pb_checked : Scalar.distance (sourceCoefficient 24 45 1 1) v2072_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2072_pg : Scalar.QComplex := ((-93086404698215871911210 : Int)/10^30,(67636276734158054288 : Int)/10^30)
theorem v2072_pg_checked : Scalar.distance (sourceCoefficient 24 45 1 2) v2072_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2072_mb : Scalar.QComplex := ((-685855513968010635137681 : Int)/10^30,(-431476970090135830014065943 : Int)/10^30)
theorem v2072_mb_checked : Scalar.distance (sourceCoefficient 24 45 3 1) v2072_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2072_mg : Scalar.QComplex := ((-93086311670832547150605 : Int)/10^30,(147965626348605069007 : Int)/10^30)
theorem v2072_mg_checked : Scalar.distance (sourceCoefficient 24 45 3 2) v2072_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2072_upper : Scalar.QComplex := ((999996992606867180114824100642 : Int)/10^30,(-2452504275475644307361902513 : Int)/10^30)
theorem v2072_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 45 5) 1) 14) v2072_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2072 : Material (24 : Basis) (45 : Basis) where
  plus := ![v2072_pa,v2072_pb,v2072_pg]
  minus := ![(Primitive.Addresses.material2072 1).one,v2072_mb,v2072_mg]
  upper := v2072_upper
  lower := (Primitive.Addresses.material2072 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2072_pa_checked.trans (by decide +kernel)
    · exact v2072_pb_checked.trans (by decide +kernel)
    · exact v2072_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 45 Primitive.Addresses.material2072
    · exact v2072_mb_checked.trans (by decide +kernel)
    · exact v2072_mg_checked.trans (by decide +kernel)
  upper_error := v2072_upper_checked
  lower_error := reuse_lower_error 24 45 Primitive.Addresses.material2072

def v2073_pa : Scalar.QComplex := ((999999724004608025799756549982 : Int)/10^30,(-742960771356700969599620813 : Int)/10^30)
theorem v2073_pa_checked : Scalar.distance (sourceCoefficient 24 46 1 0) v2073_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2073_pb : Scalar.QComplex := ((-320570866998555636972633 : Int)/10^30,(-431477395417644653665386886 : Int)/10^30)
theorem v2073_pb_checked : Scalar.distance (sourceCoefficient 24 46 1 1) v2073_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2073_pg : Scalar.QComplex := ((-93086403504701326707656 : Int)/10^30,(69159565238395326938 : Int)/10^30)
theorem v2073_pg_checked : Scalar.distance (sourceCoefficient 24 46 1 2) v2073_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2073_mb : Scalar.QComplex := ((-692916306860296396576498 : Int)/10^30,(-431476958120670604676311376 : Int)/10^30)
theorem v2073_mb_checked : Scalar.distance (sourceCoefficient 24 46 3 1) v2073_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2073_mg : Scalar.QComplex := ((-93086309162789073557740 : Int)/10^30,(149488913255703115194 : Int)/10^30)
theorem v2073_mg_checked : Scalar.distance (sourceCoefficient 24 46 3 2) v2073_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2073_upper : Scalar.QComplex := ((999996952339596853214895112915 : Int)/10^30,(-2468868469169558109399773554 : Int)/10^30)
theorem v2073_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 46 5) 1) 14) v2073_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2073 : Material (24 : Basis) (46 : Basis) where
  plus := ![v2073_pa,v2073_pb,v2073_pg]
  minus := ![(Primitive.Addresses.material2073 1).one,v2073_mb,v2073_mg]
  upper := v2073_upper
  lower := (Primitive.Addresses.material2073 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2073_pa_checked.trans (by decide +kernel)
    · exact v2073_pb_checked.trans (by decide +kernel)
    · exact v2073_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 46 Primitive.Addresses.material2073
    · exact v2073_mb_checked.trans (by decide +kernel)
    · exact v2073_mg_checked.trans (by decide +kernel)
  upper_error := v2073_upper_checked
  lower_error := reuse_lower_error 24 46 Primitive.Addresses.material2073

def v2074_pa : Scalar.QComplex := ((999999721071042693139985227819 : Int)/10^30,(-746898812967564439181384253 : Int)/10^30)
theorem v2074_pa_checked : Scalar.distance (sourceCoefficient 24 47 1 0) v2074_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2074_pb : Scalar.QComplex := ((-322270043276832619500804 : Int)/10^30,(-431477393980515923395291468 : Int)/10^30)
theorem v2074_pb_checked : Scalar.distance (sourceCoefficient 24 47 1 1) v2074_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2074_pg : Scalar.QComplex := ((-93086403213141572290734 : Int)/10^30,(69526143456170216449 : Int)/10^30)
theorem v2074_pg_checked : Scalar.distance (sourceCoefficient 24 47 1 2) v2074_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2074_mb : Scalar.QComplex := ((-694615481265715026162120 : Int)/10^30,(-431476955217229809420604864 : Int)/10^30)
theorem v2074_mb_checked : Scalar.distance (sourceCoefficient 24 47 3 1) v2074_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2074_mg : Scalar.QComplex := ((-93086308554888935832155 : Int)/10^30,(149855491085381244077 : Int)/10^30)
theorem v2074_mg_checked : Scalar.distance (sourceCoefficient 24 47 3 2) v2074_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2074_upper : Scalar.QComplex := ((999996942609333325749941622496 : Int)/10^30,(-2472806499852103561260840413 : Int)/10^30)
theorem v2074_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 47 5) 1) 14) v2074_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2074 : Material (24 : Basis) (47 : Basis) where
  plus := ![v2074_pa,v2074_pb,v2074_pg]
  minus := ![(Primitive.Addresses.material2074 1).one,v2074_mb,v2074_mg]
  upper := v2074_upper
  lower := (Primitive.Addresses.material2074 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2074_pa_checked.trans (by decide +kernel)
    · exact v2074_pb_checked.trans (by decide +kernel)
    · exact v2074_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 47 Primitive.Addresses.material2074
    · exact v2074_mb_checked.trans (by decide +kernel)
    · exact v2074_mg_checked.trans (by decide +kernel)
  upper_error := v2074_upper_checked
  lower_error := reuse_lower_error 24 47 Primitive.Addresses.material2074

def v2075_pa : Scalar.QComplex := ((999999700206966228960903983217 : Int)/10^30,(-774329372855127519080429731 : Int)/10^30)
theorem v2075_pa_checked : Scalar.distance (sourceCoefficient 24 48 1 0) v2075_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2075_pb : Scalar.QComplex := ((-334105712101684580704067 : Int)/10^30,(-431477383722635494737016934 : Int)/10^30)
theorem v2075_pb_checked : Scalar.distance (sourceCoefficient 24 48 1 1) v2075_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2075_pg : Scalar.QComplex := ((-93086401135549121499163 : Int)/10^30,(72079556221579413926 : Int)/10^30)
theorem v2075_pg_checked : Scalar.distance (sourceCoefficient 24 48 1 2) v2075_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2075_mb : Scalar.QComplex := ((-706451136831517754938122 : Int)/10^30,(-431476934745704063128580609 : Int)/10^30)
theorem v2075_mb_checked : Scalar.distance (sourceCoefficient 24 48 3 1) v2075_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2075_mg : Scalar.QComplex := ((-93086304273817043516967 : Int)/10^30,(152408901107169458522 : Int)/10^30)
theorem v2075_mg_checked : Scalar.distance (sourceCoefficient 24 48 3 2) v2075_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2075_upper : Scalar.QComplex := ((999996874402630051182064569064 : Int)/10^30,(-2500236982875566705605870249 : Int)/10^30)
theorem v2075_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 48 5) 1) 14) v2075_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2075 : Material (24 : Basis) (48 : Basis) where
  plus := ![v2075_pa,v2075_pb,v2075_pg]
  minus := ![(Primitive.Addresses.material2075 1).one,v2075_mb,v2075_mg]
  upper := v2075_upper
  lower := (Primitive.Addresses.material2075 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2075_pa_checked.trans (by decide +kernel)
    · exact v2075_pb_checked.trans (by decide +kernel)
    · exact v2075_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 48 Primitive.Addresses.material2075
    · exact v2075_mb_checked.trans (by decide +kernel)
    · exact v2075_mg_checked.trans (by decide +kernel)
  upper_error := v2075_upper_checked
  lower_error := reuse_lower_error 24 48 Primitive.Addresses.material2075

def v2076_pa : Scalar.QComplex := ((999999682899153004808299032822 : Int)/10^30,(-796367750123921226626154996 : Int)/10^30)
theorem v2076_pa_checked : Scalar.distance (sourceCoefficient 24 49 1 0) v2076_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2076_pb : Scalar.QComplex := ((-343614775452135488836342 : Int)/10^30,(-431477375167603092050588507 : Int)/10^30)
theorem v2076_pb_checked : Scalar.distance (sourceCoefficient 24 49 1 1) v2076_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2076_pg : Scalar.QComplex := ((-93086399407161764701322 : Int)/10^30,(74131029970030521361 : Int)/10^30)
theorem v2076_pg_checked : Scalar.distance (sourceCoefficient 24 49 1 2) v2076_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2076_mb : Scalar.QComplex := ((-715960189258702132871300 : Int)/10^30,(-431476917984781446747654950 : Int)/10^30)
theorem v2076_mb_checked : Scalar.distance (sourceCoefficient 24 49 3 1) v2076_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2076_mg : Scalar.QComplex := ((-93086300775100880311193 : Int)/10^30,(154460372600242687186 : Int)/10^30)
theorem v2076_mg_checked : Scalar.distance (sourceCoefficient 24 49 3 2) v2076_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2076_upper : Scalar.QComplex := ((999996819058602745014303027686 : Int)/10^30,(-2522275297449070808594260177 : Int)/10^30)
theorem v2076_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 49 5) 1) 14) v2076_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2076 : Material (24 : Basis) (49 : Basis) where
  plus := ![v2076_pa,v2076_pb,v2076_pg]
  minus := ![(Primitive.Addresses.material2076 1).one,v2076_mb,v2076_mg]
  upper := v2076_upper
  lower := (Primitive.Addresses.material2076 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2076_pa_checked.trans (by decide +kernel)
    · exact v2076_pb_checked.trans (by decide +kernel)
    · exact v2076_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 49 Primitive.Addresses.material2076
    · exact v2076_mb_checked.trans (by decide +kernel)
    · exact v2076_mg_checked.trans (by decide +kernel)
  upper_error := v2076_upper_checked
  lower_error := reuse_lower_error 24 49 Primitive.Addresses.material2076

def v2077_pa : Scalar.QComplex := ((999999680844966153762870816678 : Int)/10^30,(-798943030404883517670807145 : Int)/10^30)
theorem v2077_pa_checked : Scalar.distance (sourceCoefficient 24 50 1 0) v2077_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2077_pb : Scalar.QComplex := ((-344725950875307148932199 : Int)/10^30,(-431477374149676920776420815 : Int)/10^30)
theorem v2077_pb_checked : Scalar.distance (sourceCoefficient 24 50 1 1) v2077_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2077_pg : Scalar.QComplex := ((-93086399201750234274813 : Int)/10^30,(74370753603525445734 : Int)/10^30)
theorem v2077_pg_checked : Scalar.distance (sourceCoefficient 24 50 1 2) v2077_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2077_mb : Scalar.QComplex := ((-717071363389707959578042 : Int)/10^30,(-431476916007961309780063672 : Int)/10^30)
theorem v2077_mb_checked : Scalar.distance (sourceCoefficient 24 50 3 1) v2077_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2077_mg : Scalar.QComplex := ((-93086300362818727414323 : Int)/10^30,(154700095967216647532 : Int)/10^30)
theorem v2077_mg_checked : Scalar.distance (sourceCoefficient 24 50 3 2) v2077_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2077_upper : Scalar.QComplex := ((999996812559718816100063587097 : Int)/10^30,(-2524850570349115484288805337 : Int)/10^30)
theorem v2077_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 50 5) 1) 14) v2077_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2077 : Material (24 : Basis) (50 : Basis) where
  plus := ![v2077_pa,v2077_pb,v2077_pg]
  minus := ![(Primitive.Addresses.material2077 1).one,v2077_mb,v2077_mg]
  upper := v2077_upper
  lower := (Primitive.Addresses.material2077 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2077_pa_checked.trans (by decide +kernel)
    · exact v2077_pb_checked.trans (by decide +kernel)
    · exact v2077_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 50 Primitive.Addresses.material2077
    · exact v2077_mb_checked.trans (by decide +kernel)
    · exact v2077_mg_checked.trans (by decide +kernel)
  upper_error := v2077_upper_checked
  lower_error := reuse_lower_error 24 50 Primitive.Addresses.material2077

def v2078_pa : Scalar.QComplex := ((999999671753672198526039992543 : Int)/10^30,(-810242277258658112328612006 : Int)/10^30)
theorem v2078_pa_checked : Scalar.distance (sourceCoefficient 24 51 1 0) v2078_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2078_pb : Scalar.QComplex := ((-349601321316701831630713 : Int)/10^30,(-431477369638349287144155887 : Int)/10^30)
theorem v2078_pb_checked : Scalar.distance (sourceCoefficient 24 51 1 1) v2078_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2078_pg : Scalar.QComplex := ((-93086398291978047274782 : Int)/10^30,(75422560091077139206 : Int)/10^30)
theorem v2078_pg_checked : Scalar.distance (sourceCoefficient 24 51 1 2) v2078_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2078_mb : Scalar.QComplex := ((-721946728122706846338318 : Int)/10^30,(-431476907289410243531185538 : Int)/10^30)
theorem v2078_mb_checked : Scalar.distance (sourceCoefficient 24 51 3 1) v2078_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2078_mg : Scalar.QComplex := ((-93086298545385252012627 : Int)/10^30,(155751901278040292994 : Int)/10^30)
theorem v2078_mg_checked : Scalar.distance (sourceCoefficient 24 51 3 2) v2078_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2078_upper : Scalar.QComplex := ((999996783966963391329938042182 : Int)/10^30,(-2536149784683240582028941079 : Int)/10^30)
theorem v2078_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 51 5) 1) 14) v2078_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2078 : Material (24 : Basis) (51 : Basis) where
  plus := ![v2078_pa,v2078_pb,v2078_pg]
  minus := ![(Primitive.Addresses.material2078 1).one,v2078_mb,v2078_mg]
  upper := v2078_upper
  lower := (Primitive.Addresses.material2078 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2078_pa_checked.trans (by decide +kernel)
    · exact v2078_pb_checked.trans (by decide +kernel)
    · exact v2078_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 51 Primitive.Addresses.material2078
    · exact v2078_mb_checked.trans (by decide +kernel)
    · exact v2078_mg_checked.trans (by decide +kernel)
  upper_error := v2078_upper_checked
  lower_error := reuse_lower_error 24 51 Primitive.Addresses.material2078

def v2079_pa : Scalar.QComplex := ((999999651862224639118461068408 : Int)/10^30,(-834431201191477765464634556 : Int)/10^30)
theorem v2079_pa_checked : Scalar.distance (sourceCoefficient 24 52 1 0) v2079_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2079_pb : Scalar.QComplex := ((-360038296912512033096962 : Int)/10^30,(-431477359733773881933347772 : Int)/10^30)
theorem v2079_pb_checked : Scalar.distance (sourceCoefficient 24 52 1 1) v2079_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2079_pg : Scalar.QComplex := ((-93086396297765668193251 : Int)/10^30,(77674220518660869542 : Int)/10^30)
theorem v2079_pg_checked : Scalar.distance (sourceCoefficient 24 52 1 2) v2079_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2079_mb : Scalar.QComplex := ((-732383691285151550955602 : Int)/10^30,(-431476888378198650993500314 : Int)/10^30)
theorem v2079_mb_checked : Scalar.distance (sourceCoefficient 24 52 3 1) v2079_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2079_mg : Scalar.QComplex := ((-93086294608092077483849 : Int)/10^30,(158003559146312473020 : Int)/10^30)
theorem v2079_mg_checked : Scalar.distance (sourceCoefficient 24 52 3 2) v2079_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2079_upper : Scalar.QComplex := ((999996722327657151887621367153 : Int)/10^30,(-2560338638258665518323683556 : Int)/10^30)
theorem v2079_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 52 5) 1) 14) v2079_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2079 : Material (24 : Basis) (52 : Basis) where
  plus := ![v2079_pa,v2079_pb,v2079_pg]
  minus := ![(Primitive.Addresses.material2079 1).one,v2079_mb,v2079_mg]
  upper := v2079_upper
  lower := (Primitive.Addresses.material2079 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2079_pa_checked.trans (by decide +kernel)
    · exact v2079_pb_checked.trans (by decide +kernel)
    · exact v2079_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 52 Primitive.Addresses.material2079
    · exact v2079_mb_checked.trans (by decide +kernel)
    · exact v2079_mg_checked.trans (by decide +kernel)
  upper_error := v2079_upper_checked
  lower_error := reuse_lower_error 24 52 Primitive.Addresses.material2079

def v2080_pa : Scalar.QComplex := ((999999648765729723003156089393 : Int)/10^30,(-838133889774468594007027615 : Int)/10^30)
theorem v2080_pa_checked : Scalar.distance (sourceCoefficient 24 53 1 0) v2080_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2080_pb : Scalar.QComplex := ((-361635923586596789971814 : Int)/10^30,(-431477358187936724921071559 : Int)/10^30)
theorem v2080_pb_checked : Scalar.distance (sourceCoefficient 24 53 1 1) v2080_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2080_pg : Scalar.QComplex := ((-93086395986896335963597 : Int)/10^30,(78018890556492001753 : Int)/10^30)
theorem v2080_pg_checked : Scalar.distance (sourceCoefficient 24 53 1 2) v2080_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2080_mb : Scalar.QComplex := ((-733981316030379037342141 : Int)/10^30,(-431476885453682204266227343 : Int)/10^30)
theorem v2080_mb_checked : Scalar.distance (sourceCoefficient 24 53 3 1) v2080_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2080_mg : Scalar.QComplex := ((-93086293999788141719038 : Int)/10^30,(158348228787540965268 : Int)/10^30)
theorem v2080_mg_checked : Scalar.distance (sourceCoefficient 24 53 3 2) v2080_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2080_upper : Scalar.QComplex := ((999996712840662258679884878593 : Int)/10^30,(-2564041315982667337465061908 : Int)/10^30)
theorem v2080_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 24 53 5) 1) 14) v2080_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2080 : Material (24 : Basis) (53 : Basis) where
  plus := ![v2080_pa,v2080_pb,v2080_pg]
  minus := ![(Primitive.Addresses.material2080 1).one,v2080_mb,v2080_mg]
  upper := v2080_upper
  lower := (Primitive.Addresses.material2080 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2080_pa_checked.trans (by decide +kernel)
    · exact v2080_pb_checked.trans (by decide +kernel)
    · exact v2080_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 24 53 Primitive.Addresses.material2080
    · exact v2080_mb_checked.trans (by decide +kernel)
    · exact v2080_mg_checked.trans (by decide +kernel)
  upper_error := v2080_upper_checked
  lower_error := reuse_lower_error 24 53 Primitive.Addresses.material2080

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
