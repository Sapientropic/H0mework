import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B020

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v481_pa : Scalar.QComplex := ((999991643885523762855931505539 : Int)/10^30,(4088050773635908274667605274 : Int)/10^30)
theorem v481_pa_checked : Scalar.distance (sourceCoefficient 5 12 1 0) v481_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v481_pb : Scalar.QComplex := ((1763897287857141429911392 : Int)/10^30,(-431472759561810528745130269 : Int)/10^30)
theorem v481_pb_checked : Scalar.distance (sourceCoefficient 5 12 1 1) v481_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v481_pg : Scalar.QComplex := ((-93085527363030696258604 : Int)/10^30,(-380541541999432057624 : Int)/10^30)
theorem v481_pg_checked : Scalar.distance (sourceCoefficient 5 12 1 2) v481_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v481_mb : Scalar.QComplex := ((1391555072387435370403735 : Int)/10^30,(-431474121068699300549120845 : Int)/10^30)
theorem v481_mb_checked : Scalar.distance (sourceCoefficient 5 12 3 1) v481_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v481_mg : Scalar.QComplex := ((-93085821093246430925235 : Int)/10^30,(-300212782608651486872 : Int)/10^30)
theorem v481_mg_checked : Scalar.distance (sourceCoefficient 5 12 3 2) v481_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v481_upper : Scalar.QComplex := ((999997210120207691917117917355 : Int)/10^30,(2362149826151362109058424720 : Int)/10^30)
theorem v481_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 12 5) 1) 14) v481_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material481 : Material (5 : Basis) (12 : Basis) where
  plus := ![v481_pa,v481_pb,v481_pg]
  minus := ![(Primitive.Addresses.material481 1).one,v481_mb,v481_mg]
  upper := v481_upper
  lower := (Primitive.Addresses.material481 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v481_pa_checked.trans (by decide +kernel)
    · exact v481_pb_checked.trans (by decide +kernel)
    · exact v481_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 12 Primitive.Addresses.material481
    · exact v481_mb_checked.trans (by decide +kernel)
    · exact v481_mg_checked.trans (by decide +kernel)
  upper_error := v481_upper_checked
  lower_error := reuse_lower_error 5 12 Primitive.Addresses.material481

def v482_pa : Scalar.QComplex := ((999991853155317213492473833096 : Int)/10^30,(4036536014269503529997581909 : Int)/10^30)
theorem v482_pa_checked : Scalar.distance (sourceCoefficient 5 13 1 0) v482_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v482_pb : Scalar.QComplex := ((1741669766061358629236338 : Int)/10^30,(-431472819960328086932560900 : Int)/10^30)
theorem v482_pb_checked : Scalar.distance (sourceCoefficient 5 13 1 1) v482_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v482_pg : Scalar.QComplex := ((-93085543618268915013995 : Int)/10^30,(-375746210369013248364 : Int)/10^30)
theorem v482_pg_checked : Scalar.distance (sourceCoefficient 5 13 1 2) v482_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v482_mb : Scalar.QComplex := ((1369327506746774377763297 : Int)/10^30,(-431474162285844150267017825 : Int)/10^30)
theorem v482_mb_checked : Scalar.distance (sourceCoefficient 5 13 3 1) v482_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v482_mg : Scalar.QComplex := ((-93085833210323373780416 : Int)/10^30,(-295417438736215327065 : Int)/10^30)
theorem v482_mg_checked : Scalar.distance (sourceCoefficient 5 13 3 2) v482_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v482_upper : Scalar.QComplex := ((999997330479888175827542841728 : Int)/10^30,(2310634782329461403491020947 : Int)/10^30)
theorem v482_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 13 5) 1) 14) v482_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material482 : Material (5 : Basis) (13 : Basis) where
  plus := ![v482_pa,v482_pb,v482_pg]
  minus := ![(Primitive.Addresses.material482 1).one,v482_mb,v482_mg]
  upper := v482_upper
  lower := (Primitive.Addresses.material482 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v482_pa_checked.trans (by decide +kernel)
    · exact v482_pb_checked.trans (by decide +kernel)
    · exact v482_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 13 Primitive.Addresses.material482
    · exact v482_mb_checked.trans (by decide +kernel)
    · exact v482_mg_checked.trans (by decide +kernel)
  upper_error := v482_upper_checked
  lower_error := reuse_lower_error 5 13 Primitive.Addresses.material482

def v483_pa : Scalar.QComplex := ((999991918859549752616471154861 : Int)/10^30,(4020225814013908153718141072 : Int)/10^30)
theorem v483_pa_checked : Scalar.distance (sourceCoefficient 5 14 1 0) v483_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v483_pb : Scalar.QComplex := ((1734632262255919795558131 : Int)/10^30,(-431472838765016194324208277 : Int)/10^30)
theorem v483_pb_checked : Scalar.distance (sourceCoefficient 5 14 1 1) v483_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v483_pg : Scalar.QComplex := ((-93085548704804720799754 : Int)/10^30,(-374227950003329237568 : Int)/10^30)
theorem v483_pg_checked : Scalar.distance (sourceCoefficient 5 14 1 2) v483_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v483_mb : Scalar.QComplex := ((1362289989334120935696494 : Int)/10^30,(-431474175017476429125537664 : Int)/10^30)
theorem v483_mb_checked : Scalar.distance (sourceCoefficient 5 14 3 1) v483_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v483_mg : Scalar.QComplex := ((-93085836986666969939617 : Int)/10^30,(-293899174546397727015 : Int)/10^30)
theorem v483_mg_checked : Scalar.distance (sourceCoefficient 5 14 3 2) v483_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v483_upper : Scalar.QComplex := ((999997368034096864866512617349 : Int)/10^30,(2294324492966448656098033586 : Int)/10^30)
theorem v483_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 14 5) 1) 14) v483_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material483 : Material (5 : Basis) (14 : Basis) where
  plus := ![v483_pa,v483_pb,v483_pg]
  minus := ![(Primitive.Addresses.material483 1).one,v483_mb,v483_mg]
  upper := v483_upper
  lower := (Primitive.Addresses.material483 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v483_pa_checked.trans (by decide +kernel)
    · exact v483_pb_checked.trans (by decide +kernel)
    · exact v483_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 14 Primitive.Addresses.material483
    · exact v483_mb_checked.trans (by decide +kernel)
    · exact v483_mg_checked.trans (by decide +kernel)
  upper_error := v483_upper_checked
  lower_error := reuse_lower_error 5 14 Primitive.Addresses.material483

def v484_pa : Scalar.QComplex := ((999992024158497566012057258913 : Int)/10^30,(3993947845280444312105110883 : Int)/10^30)
theorem v484_pa_checked : Scalar.distance (sourceCoefficient 5 15 1 0) v484_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v484_pb : Scalar.QComplex := ((1723293879120018105468917 : Int)/10^30,(-431472868740020318843871522 : Int)/10^30)
theorem v484_pb_checked : Scalar.distance (sourceCoefficient 5 15 1 1) v484_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v484_pg : Scalar.QComplex := ((-93085556839140636675489 : Int)/10^30,(-371781824437321270270 : Int)/10^30)
theorem v484_pg_checked : Scalar.distance (sourceCoefficient 5 15 1 2) v484_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v484_mb : Scalar.QComplex := ((1350951584552938941421931 : Int)/10^30,(-431474195207955408117864636 : Int)/10^30)
theorem v484_mb_checked : Scalar.distance (sourceCoefficient 5 15 3 1) v484_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v484_mg : Scalar.QComplex := ((-93085843010103662971269 : Int)/10^30,(-291453042871628562893 : Int)/10^30)
theorem v484_mg_checked : Scalar.distance (sourceCoefficient 5 15 3 2) v484_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v484_upper : Scalar.QComplex := ((999997427979497732591372247967 : Int)/10^30,(2268046381634501135937864306 : Int)/10^30)
theorem v484_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 15 5) 1) 14) v484_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material484 : Material (5 : Basis) (15 : Basis) where
  plus := ![v484_pa,v484_pb,v484_pg]
  minus := ![(Primitive.Addresses.material484 1).one,v484_mb,v484_mg]
  upper := v484_upper
  lower := (Primitive.Addresses.material484 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v484_pa_checked.trans (by decide +kernel)
    · exact v484_pb_checked.trans (by decide +kernel)
    · exact v484_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 15 Primitive.Addresses.material484
    · exact v484_mb_checked.trans (by decide +kernel)
    · exact v484_mg_checked.trans (by decide +kernel)
  upper_error := v484_upper_checked
  lower_error := reuse_lower_error 5 15 Primitive.Addresses.material484

def v485_pa : Scalar.QComplex := ((999992037462607995325900659005 : Int)/10^30,(3990615413944023386925379407 : Int)/10^30)
theorem v485_pa_checked : Scalar.distance (sourceCoefficient 5 16 1 0) v485_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v485_pb : Scalar.QComplex := ((1721856006091536898389796 : Int)/10^30,(-431472872512905383354035287 : Int)/10^30)
theorem v485_pb_checked : Scalar.distance (sourceCoefficient 5 16 1 1) v485_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v485_pg : Scalar.QComplex := ((-93085557865335383448406 : Int)/10^30,(-371471619889649143092 : Int)/10^30)
theorem v485_pg_checked : Scalar.distance (sourceCoefficient 5 16 1 2) v485_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v485_mb : Scalar.QComplex := ((1349513708804013690653247 : Int)/10^30,(-431474197740019403628428777 : Int)/10^30)
theorem v485_mb_checked : Scalar.distance (sourceCoefficient 5 16 3 1) v485_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v485_mg : Scalar.QComplex := ((-93085843768605474098132 : Int)/10^30,(-291142837553899917491 : Int)/10^30)
theorem v485_mg_checked : Scalar.distance (sourceCoefficient 5 16 3 2) v485_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v485_upper : Scalar.QComplex := ((999997435532114176142303520300 : Int)/10^30,(2264713932299657569948479049 : Int)/10^30)
theorem v485_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 16 5) 1) 14) v485_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material485 : Material (5 : Basis) (16 : Basis) where
  plus := ![v485_pa,v485_pb,v485_pg]
  minus := ![(Primitive.Addresses.material485 1).one,v485_mb,v485_mg]
  upper := v485_upper
  lower := (Primitive.Addresses.material485 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v485_pa_checked.trans (by decide +kernel)
    · exact v485_pb_checked.trans (by decide +kernel)
    · exact v485_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 16 Primitive.Addresses.material485
    · exact v485_mb_checked.trans (by decide +kernel)
    · exact v485_mg_checked.trans (by decide +kernel)
  upper_error := v485_upper_checked
  lower_error := reuse_lower_error 5 16 Primitive.Addresses.material485

def v486_pa : Scalar.QComplex := ((999992064143197231462810601524 : Int)/10^30,(3983924023838040053333777106 : Int)/10^30)
theorem v486_pa_checked : Scalar.distance (sourceCoefficient 5 17 1 0) v486_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v486_pb : Scalar.QComplex := ((1718968814033488400873682 : Int)/10^30,(-431472880069414981116166752 : Int)/10^30)
theorem v486_pb_checked : Scalar.distance (sourceCoefficient 5 17 1 1) v486_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v486_pg : Scalar.QComplex := ((-93085559922251592028984 : Int)/10^30,(-370848741449181184971 : Int)/10^30)
theorem v486_pg_checked : Scalar.distance (sourceCoefficient 5 17 1 2) v486_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v486_mb : Scalar.QComplex := ((1346626511300071297233988 : Int)/10^30,(-431474202805009475964028360 : Int)/10^30)
theorem v486_mb_checked : Scalar.distance (sourceCoefficient 5 17 3 1) v486_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v486_mg : Scalar.QComplex := ((-93085845288004876074519 : Int)/10^30,(-290519957570332021770 : Int)/10^30)
theorem v486_mg_checked : Scalar.distance (sourceCoefficient 5 17 3 2) v486_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v486_upper : Scalar.QComplex := ((999997450663931389916927494342 : Int)/10^30,(2258022506111437195897619287 : Int)/10^30)
theorem v486_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 17 5) 1) 14) v486_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material486 : Material (5 : Basis) (17 : Basis) where
  plus := ![v486_pa,v486_pb,v486_pg]
  minus := ![(Primitive.Addresses.material486 1).one,v486_mb,v486_mg]
  upper := v486_upper
  lower := (Primitive.Addresses.material486 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v486_pa_checked.trans (by decide +kernel)
    · exact v486_pb_checked.trans (by decide +kernel)
    · exact v486_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 17 Primitive.Addresses.material486
    · exact v486_mb_checked.trans (by decide +kernel)
    · exact v486_mg_checked.trans (by decide +kernel)
  upper_error := v486_upper_checked
  lower_error := reuse_lower_error 5 17 Primitive.Addresses.material486

def v487_pa : Scalar.QComplex := ((999992152815724526323180701865 : Int)/10^30,(3961604090850863961085280834 : Int)/10^30)
theorem v487_pa_checked : Scalar.distance (sourceCoefficient 5 18 1 0) v487_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v487_pb : Scalar.QComplex := ((1709338239383212532004098 : Int)/10^30,(-431472905088790493720006246 : Int)/10^30)
theorem v487_pb_checked : Scalar.distance (sourceCoefficient 5 18 1 1) v487_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v487_pg : Scalar.QComplex := ((-93085566748179949686362 : Int)/10^30,(-368771055843191505294 : Int)/10^30)
theorem v487_pg_checked : Scalar.distance (sourceCoefficient 5 18 1 2) v487_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v487_mb : Scalar.QComplex := ((1336995918645104273132983 : Int)/10^30,(-431474219513623494503725612 : Int)/10^30)
theorem v487_mb_checked : Scalar.distance (sourceCoefficient 5 18 3 1) v487_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v487_mg : Scalar.QComplex := ((-93085850320981589643724 : Int)/10^30,(-288442266847490903869 : Int)/10^30)
theorem v487_mg_checked : Scalar.distance (sourceCoefficient 5 18 3 2) v487_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v487_upper : Scalar.QComplex := ((999997500814147130101511566012 : Int)/10^30,(2235702453326441602450466511 : Int)/10^30)
theorem v487_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 18 5) 1) 14) v487_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material487 : Material (5 : Basis) (18 : Basis) where
  plus := ![v487_pa,v487_pb,v487_pg]
  minus := ![(Primitive.Addresses.material487 1).one,v487_mb,v487_mg]
  upper := v487_upper
  lower := (Primitive.Addresses.material487 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v487_pa_checked.trans (by decide +kernel)
    · exact v487_pb_checked.trans (by decide +kernel)
    · exact v487_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 18 Primitive.Addresses.material487
    · exact v487_mb_checked.trans (by decide +kernel)
    · exact v487_mg_checked.trans (by decide +kernel)
  upper_error := v487_upper_checked
  lower_error := reuse_lower_error 5 18 Primitive.Addresses.material487

def v488_pa : Scalar.QComplex := ((999992214698885932258107360677 : Int)/10^30,(3945952561451042974367393254 : Int)/10^30)
theorem v488_pa_checked : Scalar.distance (sourceCoefficient 5 19 1 0) v488_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v488_pb : Scalar.QComplex := ((1702584938723326466543423 : Int)/10^30,(-431472922462306661918693266 : Int)/10^30)
theorem v488_pb_checked : Scalar.distance (sourceCoefficient 5 19 1 1) v488_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v488_pg : Scalar.QComplex := ((-93085571502491175272345 : Int)/10^30,(-367314108955330926725 : Int)/10^30)
theorem v488_pg_checked : Scalar.distance (sourceCoefficient 5 19 1 2) v488_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v488_mb : Scalar.QComplex := ((1330242605507218705401170 : Int)/10^30,(-431474231059338881637528736 : Int)/10^30)
theorem v488_mb_checked : Scalar.distance (sourceCoefficient 5 19 3 1) v488_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v488_mg : Scalar.QComplex := ((-93085853818011499210634 : Int)/10^30,(-286985316399361775960 : Int)/10^30)
theorem v488_mg_checked : Scalar.distance (sourceCoefficient 5 19 3 2) v488_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v488_upper : Scalar.QComplex := ((999997535684096519901343378290 : Int)/10^30,(2220050840433012508875923313 : Int)/10^30)
theorem v488_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 19 5) 1) 14) v488_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material488 : Material (5 : Basis) (19 : Basis) where
  plus := ![v488_pa,v488_pb,v488_pg]
  minus := ![(Primitive.Addresses.material488 1).one,v488_mb,v488_mg]
  upper := v488_upper
  lower := (Primitive.Addresses.material488 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v488_pa_checked.trans (by decide +kernel)
    · exact v488_pb_checked.trans (by decide +kernel)
    · exact v488_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 19 Primitive.Addresses.material488
    · exact v488_mb_checked.trans (by decide +kernel)
    · exact v488_mg_checked.trans (by decide +kernel)
  upper_error := v488_upper_checked
  lower_error := reuse_lower_error 5 19 Primitive.Addresses.material488

def v489_pa : Scalar.QComplex := ((999992225765056670080511061949 : Int)/10^30,(3943147150174703394709615883 : Int)/10^30)
theorem v489_pa_checked : Scalar.distance (sourceCoefficient 5 20 1 0) v489_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v489_pb : Scalar.QComplex := ((1701374463690081627836805 : Int)/10^30,(-431472925561475567652102012 : Int)/10^30)
theorem v489_pb_checked : Scalar.distance (sourceCoefficient 5 20 1 1) v489_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v489_pg : Scalar.QComplex := ((-93085572351851681067543 : Int)/10^30,(-367052962897555329868 : Int)/10^30)
theorem v489_pg_checked : Scalar.distance (sourceCoefficient 5 20 1 2) v489_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v489_mb : Scalar.QComplex := ((1329032128250245858751637 : Int)/10^30,(-431474233113921197490121590 : Int)/10^30)
theorem v489_mb_checked : Scalar.distance (sourceCoefficient 5 20 3 1) v489_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v489_mg : Scalar.QComplex := ((-93085854442014402471590 : Int)/10^30,(-286724169705862928653 : Int)/10^30)
theorem v489_mg_checked : Scalar.distance (sourceCoefficient 5 20 3 2) v489_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v489_upper : Scalar.QComplex := ((999997541908365417923148505033 : Int)/10^30,(2217245414235796700253745392 : Int)/10^30)
theorem v489_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 20 5) 1) 14) v489_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material489 : Material (5 : Basis) (20 : Basis) where
  plus := ![v489_pa,v489_pb,v489_pg]
  minus := ![(Primitive.Addresses.material489 1).one,v489_mb,v489_mg]
  upper := v489_upper
  lower := (Primitive.Addresses.material489 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v489_pa_checked.trans (by decide +kernel)
    · exact v489_pb_checked.trans (by decide +kernel)
    · exact v489_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 20 Primitive.Addresses.material489
    · exact v489_mb_checked.trans (by decide +kernel)
    · exact v489_mg_checked.trans (by decide +kernel)
  upper_error := v489_upper_checked
  lower_error := reuse_lower_error 5 20 Primitive.Addresses.material489

def v490_pa : Scalar.QComplex := ((999992433381687981282749180810 : Int)/10^30,(3890138734071672504090610354 : Int)/10^30)
theorem v490_pa_checked : Scalar.distance (sourceCoefficient 5 21 1 0) v490_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v490_pb : Scalar.QComplex := ((1678502465509228180707302 : Int)/10^30,(-431472983269395949737773335 : Int)/10^30)
theorem v490_pb_checked : Scalar.distance (sourceCoefficient 5 21 1 1) v490_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v490_pg : Scalar.QComplex := ((-93085588239913104699384 : Int)/10^30,(-362118592409104975765 : Int)/10^30)
theorem v490_pg_checked : Scalar.distance (sourceCoefficient 5 21 1 2) v490_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v490_mb : Scalar.QComplex := ((1306160088786346414821827 : Int)/10^30,(-431474271084315778761469059 : Int)/10^30)
theorem v490_mb_checked : Scalar.distance (sourceCoefficient 5 21 3 1) v490_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v490_mg : Scalar.QComplex := ((-93085866071930414516406 : Int)/10^30,(-281789787344022782401 : Int)/10^30)
theorem v490_mg_checked : Scalar.distance (sourceCoefficient 5 21 3 2) v490_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v490_upper : Scalar.QComplex := ((999997658036970200654005555495 : Int)/10^30,(2164236718755103979662370299 : Int)/10^30)
theorem v490_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 21 5) 1) 14) v490_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material490 : Material (5 : Basis) (21 : Basis) where
  plus := ![v490_pa,v490_pb,v490_pg]
  minus := ![(Primitive.Addresses.material490 1).one,v490_mb,v490_mg]
  upper := v490_upper
  lower := (Primitive.Addresses.material490 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v490_pa_checked.trans (by decide +kernel)
    · exact v490_pb_checked.trans (by decide +kernel)
    · exact v490_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 21 Primitive.Addresses.material490
    · exact v490_mb_checked.trans (by decide +kernel)
    · exact v490_mg_checked.trans (by decide +kernel)
  upper_error := v490_upper_checked
  lower_error := reuse_lower_error 5 21 Primitive.Addresses.material490

def v491_pa : Scalar.QComplex := ((999992438803951199786733622746 : Int)/10^30,(3888744646529871873787809644 : Int)/10^30)
theorem v491_pa_checked : Scalar.distance (sourceCoefficient 5 22 1 0) v491_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v491_pb : Scalar.QComplex := ((1677900946566181102286415 : Int)/10^30,(-431472984765260991892268625 : Int)/10^30)
theorem v491_pb_checked : Scalar.distance (sourceCoefficient 5 22 1 1) v491_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v491_pg : Scalar.QComplex := ((-93085588653640656861053 : Int)/10^30,(-361988821614374588513 : Int)/10^30)
theorem v491_pg_checked : Scalar.distance (sourceCoefficient 5 22 1 2) v491_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v491_mb : Scalar.QComplex := ((1305558568776408169552368 : Int)/10^30,(-431474272061096507494930589 : Int)/10^30)
theorem v491_mb_checked : Scalar.distance (sourceCoefficient 5 22 3 1) v491_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v491_mg : Scalar.QComplex := ((-93085866373671461435706 : Int)/10^30,(-281660016240583748928 : Int)/10^30)
theorem v491_mg_checked : Scalar.distance (sourceCoefficient 5 22 3 2) v491_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v491_upper : Scalar.QComplex := ((999997661053156716819839691351 : Int)/10^30,(2162842623931298570584127174 : Int)/10^30)
theorem v491_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 22 5) 1) 14) v491_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material491 : Material (5 : Basis) (22 : Basis) where
  plus := ![v491_pa,v491_pb,v491_pg]
  minus := ![(Primitive.Addresses.material491 1).one,v491_mb,v491_mg]
  upper := v491_upper
  lower := (Primitive.Addresses.material491 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v491_pa_checked.trans (by decide +kernel)
    · exact v491_pb_checked.trans (by decide +kernel)
    · exact v491_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 22 Primitive.Addresses.material491
    · exact v491_mb_checked.trans (by decide +kernel)
    · exact v491_mg_checked.trans (by decide +kernel)
  upper_error := v491_upper_checked
  lower_error := reuse_lower_error 5 22 Primitive.Addresses.material491

def v492_pa : Scalar.QComplex := ((999992478838900835705530218568 : Int)/10^30,(3878435977357923251104449439 : Int)/10^30)
theorem v492_pa_checked : Scalar.distance (sourceCoefficient 5 23 1 0) v492_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v492_pb : Scalar.QComplex := ((1673452976446855125537197 : Int)/10^30,(-431472995791827447595515446 : Int)/10^30)
theorem v492_pb_checked : Scalar.distance (sourceCoefficient 5 23 1 1) v492_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v492_pg : Scalar.QComplex := ((-93085591706424475842047 : Int)/10^30,(-361029223206796251213 : Int)/10^30)
theorem v492_pg_checked : Scalar.distance (sourceCoefficient 5 23 1 2) v492_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v492_mb : Scalar.QComplex := ((1301110590797834517350944 : Int)/10^30,(-431474279249260973662836330 : Int)/10^30)
theorem v492_mb_checked : Scalar.distance (sourceCoefficient 5 23 3 1) v492_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v492_mg : Scalar.QComplex := ((-93085868598363936693584 : Int)/10^30,(-280700415555892811081 : Int)/10^30)
theorem v492_mg_checked : Scalar.distance (sourceCoefficient 5 23 3 2) v492_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v492_upper : Scalar.QComplex := ((999997683296218929762601854579 : Int)/10^30,(2152533901016210608837265066 : Int)/10^30)
theorem v492_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 23 5) 1) 14) v492_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material492 : Material (5 : Basis) (23 : Basis) where
  plus := ![v492_pa,v492_pb,v492_pg]
  minus := ![(Primitive.Addresses.material492 1).one,v492_mb,v492_mg]
  upper := v492_upper
  lower := (Primitive.Addresses.material492 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v492_pa_checked.trans (by decide +kernel)
    · exact v492_pb_checked.trans (by decide +kernel)
    · exact v492_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 23 Primitive.Addresses.material492
    · exact v492_mb_checked.trans (by decide +kernel)
    · exact v492_mg_checked.trans (by decide +kernel)
  upper_error := v492_upper_checked
  lower_error := reuse_lower_error 5 23 Primitive.Addresses.material492

def v493_pa : Scalar.QComplex := ((999992675131871885066091827378 : Int)/10^30,(3827490379156657467765887902 : Int)/10^30)
theorem v493_pa_checked : Scalar.distance (sourceCoefficient 5 24 1 0) v493_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v493_pb : Scalar.QComplex := ((1651471042204070354212719 : Int)/10^30,(-431473049387611624232537187 : Int)/10^30)
theorem v493_pb_checked : Scalar.distance (sourceCoefficient 5 24 1 1) v493_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v493_pg : Scalar.QComplex := ((-93085606623872729135608 : Int)/10^30,(-356286873545198594847 : Int)/10^30)
theorem v493_pg_checked : Scalar.distance (sourceCoefficient 5 24 1 2) v493_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v493_mb : Scalar.QComplex := ((1279128618489180608714269 : Int)/10^30,(-431474313875605972183373100 : Int)/10^30)
theorem v493_mb_checked : Scalar.distance (sourceCoefficient 5 24 3 1) v493_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v493_mg : Scalar.QComplex := ((-93085879423372465080639 : Int)/10^30,(-275958054787002684151 : Int)/10^30)
theorem v493_mg_checked : Scalar.distance (sourceCoefficient 5 24 3 2) v493_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v493_upper : Scalar.QComplex := ((999997791661416876981935845261 : Int)/10^30,(2101588039908568383964098267 : Int)/10^30)
theorem v493_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 24 5) 1) 14) v493_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material493 : Material (5 : Basis) (24 : Basis) where
  plus := ![v493_pa,v493_pb,v493_pg]
  minus := ![(Primitive.Addresses.material493 1).one,v493_mb,v493_mg]
  upper := v493_upper
  lower := (Primitive.Addresses.material493 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v493_pa_checked.trans (by decide +kernel)
    · exact v493_pb_checked.trans (by decide +kernel)
    · exact v493_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 24 Primitive.Addresses.material493
    · exact v493_mb_checked.trans (by decide +kernel)
    · exact v493_mg_checked.trans (by decide +kernel)
  upper_error := v493_upper_checked
  lower_error := reuse_lower_error 5 24 Primitive.Addresses.material493

def v494_pa : Scalar.QComplex := ((999992762840070708373900146331 : Int)/10^30,(3804506207393991104635569294 : Int)/10^30)
theorem v494_pa_checked : Scalar.distance (sourceCoefficient 5 25 1 0) v494_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v494_pb : Scalar.QComplex := ((1641553865038851570504362 : Int)/10^30,(-431473073078627043189114835 : Int)/10^30)
theorem v494_pb_checked : Scalar.distance (sourceCoefficient 5 25 1 1) v494_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v494_pg : Scalar.QComplex := ((-93085613261628630790769 : Int)/10^30,(-354147356494000027301 : Int)/10^30)
theorem v494_pg_checked : Scalar.distance (sourceCoefficient 5 25 1 2) v494_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v494_mb : Scalar.QComplex := ((1269211424572300818169600 : Int)/10^30,(-431474329008535329387346825 : Int)/10^30)
theorem v494_mb_checked : Scalar.distance (sourceCoefficient 5 25 3 1) v494_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v494_mg : Scalar.QComplex := ((-93085884214819040282478 : Int)/10^30,(-273818532804359705825 : Int)/10^30)
theorem v494_mg_checked : Scalar.distance (sourceCoefficient 5 25 3 2) v494_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v494_upper : Scalar.QComplex := ((999997839700889714642723876158 : Int)/10^30,(2078603751001731607464380623 : Int)/10^30)
theorem v494_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 25 5) 1) 14) v494_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material494 : Material (5 : Basis) (25 : Basis) where
  plus := ![v494_pa,v494_pb,v494_pg]
  minus := ![(Primitive.Addresses.material494 1).one,v494_mb,v494_mg]
  upper := v494_upper
  lower := (Primitive.Addresses.material494 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v494_pa_checked.trans (by decide +kernel)
    · exact v494_pb_checked.trans (by decide +kernel)
    · exact v494_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 25 Primitive.Addresses.material494
    · exact v494_mb_checked.trans (by decide +kernel)
    · exact v494_mg_checked.trans (by decide +kernel)
  upper_error := v494_upper_checked
  lower_error := reuse_lower_error 5 25 Primitive.Addresses.material494

def v495_pa : Scalar.QComplex := ((999992790753134824509807036437 : Int)/10^30,(3797162329570677880804523975 : Int)/10^30)
theorem v495_pa_checked : Scalar.distance (sourceCoefficient 5 26 1 0) v495_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v495_pb : Scalar.QComplex := ((1638385139341394911682863 : Int)/10^30,(-431473080584286240392349254 : Int)/10^30)
theorem v495_pb_checked : Scalar.distance (sourceCoefficient 5 26 1 1) v495_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v495_pg : Scalar.QComplex := ((-93085615370422920801039 : Int)/10^30,(-353463740316837029738 : Int)/10^30)
theorem v495_pg_checked : Scalar.distance (sourceCoefficient 5 26 1 2) v495_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v495_mb : Scalar.QComplex := ((1266042693577659709584868 : Int)/10^30,(-431474333779724169093156739 : Int)/10^30)
theorem v495_mb_checked : Scalar.distance (sourceCoefficient 5 26 3 1) v495_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v495_mg : Scalar.QComplex := ((-93085885733682573130271 : Int)/10^30,(-273134915061943758113 : Int)/10^30)
theorem v495_mg_checked : Scalar.distance (sourceCoefficient 5 26 3 2) v495_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v495_upper : Scalar.QComplex := ((999997854939045365901721237781 : Int)/10^30,(2071259835940845317914981263 : Int)/10^30)
theorem v495_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 26 5) 1) 14) v495_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material495 : Material (5 : Basis) (26 : Basis) where
  plus := ![v495_pa,v495_pb,v495_pg]
  minus := ![(Primitive.Addresses.material495 1).one,v495_mb,v495_mg]
  upper := v495_upper
  lower := (Primitive.Addresses.material495 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v495_pa_checked.trans (by decide +kernel)
    · exact v495_pb_checked.trans (by decide +kernel)
    · exact v495_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 26 Primitive.Addresses.material495
    · exact v495_mb_checked.trans (by decide +kernel)
    · exact v495_mg_checked.trans (by decide +kernel)
  upper_error := v495_upper_checked
  lower_error := reuse_lower_error 5 26 Primitive.Addresses.material495

def v496_pa : Scalar.QComplex := ((999992809897978241314156577509 : Int)/10^30,(3792117132414330946928624388 : Int)/10^30)
theorem v496_pa_checked : Scalar.distance (sourceCoefficient 5 27 1 0) v496_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v496_pb : Scalar.QComplex := ((1636208245048734173048708 : Int)/10^30,(-431473085722646074038035483 : Int)/10^30)
theorem v496_pb_checked : Scalar.distance (sourceCoefficient 5 27 1 1) v496_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v496_pg : Scalar.QComplex := ((-93085616815756994956208 : Int)/10^30,(-352994100371982393362 : Int)/10^30)
theorem v496_pg_checked : Scalar.distance (sourceCoefficient 5 27 1 2) v496_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v496_mb : Scalar.QComplex := ((1263865795661383091792185 : Int)/10^30,(-431474337039520358605813797 : Int)/10^30)
theorem v496_mb_checked : Scalar.distance (sourceCoefficient 5 27 3 1) v496_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v496_mg : Scalar.QComplex := ((-93085886773737988509883 : Int)/10^30,(-272665274044699326247 : Int)/10^30)
theorem v496_mg_checked : Scalar.distance (sourceCoefficient 5 27 3 2) v496_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v496_upper : Scalar.QComplex := ((999997865376307673566598162402 : Int)/10^30,(2066214613256463967151705287 : Int)/10^30)
theorem v496_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 27 5) 1) 14) v496_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material496 : Material (5 : Basis) (27 : Basis) where
  plus := ![v496_pa,v496_pb,v496_pg]
  minus := ![(Primitive.Addresses.material496 1).one,v496_mb,v496_mg]
  upper := v496_upper
  lower := (Primitive.Addresses.material496 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v496_pa_checked.trans (by decide +kernel)
    · exact v496_pb_checked.trans (by decide +kernel)
    · exact v496_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 27 Primitive.Addresses.material496
    · exact v496_mb_checked.trans (by decide +kernel)
    · exact v496_mg_checked.trans (by decide +kernel)
  upper_error := v496_upper_checked
  lower_error := reuse_lower_error 5 27 Primitive.Addresses.material496

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
