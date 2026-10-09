import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B052
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B053

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1265_pa : Scalar.QComplex := ((999998860519088426597459188629 : Int)/10^30,(-1509622643156248250062154204 : Int)/10^30)
theorem v1265_pa_checked : Scalar.distance (sourceCoefficient 13 96 1 0) v1265_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1265_pb : Scalar.QComplex := ((-651367996204727993190613 : Int)/10^30,(-431476870684373009964069991 : Int)/10^30)
theorem v1265_pb_checked : Scalar.distance (sourceCoefficient 13 96 1 1) v1265_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1265_pg : Scalar.QComplex := ((-93086306712653264326487 : Int)/10^30,(140525356507170166931 : Int)/10^30)
theorem v1265_pg_checked : Scalar.distance (sourceCoefficient 13 96 1 2) v1265_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1265_mb : Scalar.QComplex := ((-1023712860074399054417100 : Int)/10^30,(-431476147924570387866065812 : Int)/10^30)
theorem v1265_mb_checked : Scalar.distance (sourceCoefficient 13 96 3 1) v1265_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1265_mg : Scalar.QComplex := ((-93086150785313382249177 : Int)/10^30,(220854594424554162219 : Int)/10^30)
theorem v1265_mg_checked : Scalar.distance (sourceCoefficient 13 96 3 2) v1265_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1265_upper : Scalar.QComplex := ((999994765666523609950189270915 : Int)/10^30,(-3235527708818633740354893279 : Int)/10^30)
theorem v1265_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 96 5) 1) 14) v1265_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1265 : Material (13 : Basis) (96 : Basis) where
  plus := ![v1265_pa,v1265_pb,v1265_pg]
  minus := ![(Primitive.Addresses.material1265 1).one,v1265_mb,v1265_mg]
  upper := v1265_upper
  lower := (Primitive.Addresses.material1265 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1265_pa_checked.trans (by decide +kernel)
    · exact v1265_pb_checked.trans (by decide +kernel)
    · exact v1265_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 96 Primitive.Addresses.material1265
    · exact v1265_mb_checked.trans (by decide +kernel)
    · exact v1265_mg_checked.trans (by decide +kernel)
  upper_error := v1265_upper_checked
  lower_error := reuse_lower_error 13 96 Primitive.Addresses.material1265

def v1266_pa : Scalar.QComplex := ((999998747395387195418634336484 : Int)/10^30,(-1582784778986343017205512730 : Int)/10^30)
theorem v1266_pa_checked : Scalar.distance (sourceCoefficient 13 97 1 0) v1266_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1266_pb : Scalar.QComplex := ((-682935776248598565727378 : Int)/10^30,(-431476805859520878529499640 : Int)/10^30)
theorem v1266_pb_checked : Scalar.distance (sourceCoefficient 13 97 1 1) v1266_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1266_pg : Scalar.QComplex := ((-93086294454895455098697 : Int)/10^30,(147335754548895129434 : Int)/10^30)
theorem v1266_pg_checked : Scalar.distance (sourceCoefficient 13 97 1 2) v1266_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1266_mb : Scalar.QComplex := ((-1055280572423214611332299 : Int)/10^30,(-431476055858169975861244566 : Int)/10^30)
theorem v1266_mb_checked : Scalar.distance (sourceCoefficient 13 97 3 1) v1266_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1266_mg : Scalar.QComplex := ((-93086132650493356077669 : Int)/10^30,(227664979352563762776 : Int)/10^30)
theorem v1266_mg_checked : Scalar.distance (sourceCoefficient 13 97 3 2) v1266_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1266_upper : Scalar.QComplex := ((999994526271781637607748138176 : Int)/10^30,(-3308689540441075593753076376 : Int)/10^30)
theorem v1266_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 97 5) 1) 14) v1266_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1266 : Material (13 : Basis) (97 : Basis) where
  plus := ![v1266_pa,v1266_pb,v1266_pg]
  minus := ![(Primitive.Addresses.material1266 1).one,v1266_mb,v1266_mg]
  upper := v1266_upper
  lower := (Primitive.Addresses.material1266 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1266_pa_checked.trans (by decide +kernel)
    · exact v1266_pb_checked.trans (by decide +kernel)
    · exact v1266_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 97 Primitive.Addresses.material1266
    · exact v1266_mb_checked.trans (by decide +kernel)
    · exact v1266_mg_checked.trans (by decide +kernel)
  upper_error := v1266_upper_checked
  lower_error := reuse_lower_error 13 97 Primitive.Addresses.material1266

def v1267_pa : Scalar.QComplex := ((999999996540092625063865786586 : Int)/10^30,(-83185423830748794133966395 : Int)/10^30)
theorem v1267_pa_checked : Scalar.distance (sourceCoefficient 14 15 1 0) v1267_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1267_pb : Scalar.QComplex := ((-35892640453749205903918 : Int)/10^30,(-431477519458121472872842554 : Int)/10^30)
theorem v1267_pb_checked : Scalar.distance (sourceCoefficient 14 15 1 1) v1267_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1267_pg : Scalar.QComplex := ((-93086429569548945261509 : Int)/10^30,(7743434123425640877 : Int)/10^30)
theorem v1267_pg_checked : Scalar.distance (sourceCoefficient 14 15 1 2) v1267_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1267_mb : Scalar.QComplex := ((-408238293355549065104512 : Int)/10^30,(-431477327825589314743594193 : Int)/10^30)
theorem v1267_mb_checked : Scalar.distance (sourceCoefficient 14 15 3 1) v1267_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1267_mg : Scalar.QComplex := ((-93086388226982059332734 : Int)/10^30,(88072827501555476743 : Int)/10^30)
theorem v1267_mg_checked : Scalar.distance (sourceCoefficient 14 15 3 2) v1267_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1267_upper : Scalar.QComplex := ((999998363587071020711399965533 : Int)/10^30,(-1809094574673005609556861421 : Int)/10^30)
theorem v1267_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 15 5) 1) 14) v1267_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1267 : Material (14 : Basis) (15 : Basis) where
  plus := ![v1267_pa,v1267_pb,v1267_pg]
  minus := ![(Primitive.Addresses.material1267 1).one,v1267_mb,v1267_mg]
  upper := v1267_upper
  lower := (Primitive.Addresses.material1267 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1267_pa_checked.trans (by decide +kernel)
    · exact v1267_pb_checked.trans (by decide +kernel)
    · exact v1267_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 15 Primitive.Addresses.material1267
    · exact v1267_mb_checked.trans (by decide +kernel)
    · exact v1267_mg_checked.trans (by decide +kernel)
  upper_error := v1267_upper_checked
  lower_error := reuse_lower_error 14 15 Primitive.Addresses.material1267

def v1268_pa : Scalar.QComplex := ((999999996257328065016820983305 : Int)/10^30,(-86517881712156850635954577 : Int)/10^30)
theorem v1268_pa_checked : Scalar.distance (sourceCoefficient 14 16 1 0) v1268_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1268_pb : Scalar.QComplex := ((-37330521117933971027778 : Int)/10^30,(-431477519322721346357359325 : Int)/10^30)
theorem v1268_pb_checked : Scalar.distance (sourceCoefficient 14 16 1 1) v1268_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1268_pg : Scalar.QComplex := ((-93086429541782645164029 : Int)/10^30,(8053640730245109057 : Int)/10^30)
theorem v1268_pg_checked : Scalar.distance (sourceCoefficient 14 16 1 2) v1268_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1268_mb : Scalar.QComplex := ((-409676173367500933572134 : Int)/10^30,(-431477326449362985193434146 : Int)/10^30)
theorem v1268_mb_checked : Scalar.distance (sourceCoefficient 14 16 3 1) v1268_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1268_mg : Scalar.QComplex := ((-93086387931521439075651 : Int)/10^30,(88383033968909781625 : Int)/10^30)
theorem v1268_mg_checked : Scalar.distance (sourceCoefficient 14 16 3 2) v1268_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1268_upper : Scalar.QComplex := ((999998357552786896716066995505 : Int)/10^30,(-1812427027103083131262028555 : Int)/10^30)
theorem v1268_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 16 5) 1) 14) v1268_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1268 : Material (14 : Basis) (16 : Basis) where
  plus := ![v1268_pa,v1268_pb,v1268_pg]
  minus := ![(Primitive.Addresses.material1268 1).one,v1268_mb,v1268_mg]
  upper := v1268_upper
  lower := (Primitive.Addresses.material1268 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1268_pa_checked.trans (by decide +kernel)
    · exact v1268_pb_checked.trans (by decide +kernel)
    · exact v1268_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 16 Primitive.Addresses.material1268
    · exact v1268_mb_checked.trans (by decide +kernel)
    · exact v1268_mg_checked.trans (by decide +kernel)
  upper_error := v1268_upper_checked
  lower_error := reuse_lower_error 14 16 Primitive.Addresses.material1268

def v1269_pa : Scalar.QComplex := ((999999995656010858700883071958 : Int)/10^30,(-93209324982686105687708581 : Int)/10^30)
theorem v1269_pa_checked : Scalar.distance (sourceCoefficient 14 17 1 0) v1269_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1269_pb : Scalar.QComplex := ((-40217728468840174935399 : Int)/10^30,(-431477519031549207567831453 : Int)/10^30)
theorem v1269_pb_checked : Scalar.distance (sourceCoefficient 14 17 1 1) v1269_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1269_pg : Scalar.QComplex := ((-93086429482386849590768 : Int)/10^30,(8676523294792412014 : Int)/10^30)
theorem v1269_pg_checked : Scalar.distance (sourceCoefficient 14 17 1 2) v1269_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1269_mb : Scalar.QComplex := ((-412563379392099446973841 : Int)/10^30,(-431477323666661045980505810 : Int)/10^30)
theorem v1269_mb_checked : Scalar.distance (sourceCoefficient 14 17 3 1) v1269_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1269_mg : Scalar.QComplex := ((-93086387334606066003147 : Int)/10^30,(89005916250273542169 : Int)/10^30)
theorem v1269_mg_checked : Scalar.distance (sourceCoefficient 14 17 3 2) v1269_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1269_upper : Scalar.QComplex := ((999998345402646544049520786682 : Int)/10^30,(-1819118459369674719972278541 : Int)/10^30)
theorem v1269_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 17 5) 1) 14) v1269_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1269 : Material (14 : Basis) (17 : Basis) where
  plus := ![v1269_pa,v1269_pb,v1269_pg]
  minus := ![(Primitive.Addresses.material1269 1).one,v1269_mb,v1269_mg]
  upper := v1269_upper
  lower := (Primitive.Addresses.material1269 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1269_pa_checked.trans (by decide +kernel)
    · exact v1269_pb_checked.trans (by decide +kernel)
    · exact v1269_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 17 Primitive.Addresses.material1269
    · exact v1269_mb_checked.trans (by decide +kernel)
    · exact v1269_mg_checked.trans (by decide +kernel)
  upper_error := v1269_upper_checked
  lower_error := reuse_lower_error 14 17 Primitive.Addresses.material1269

def v1270_pa : Scalar.QComplex := ((999999993326474919110836857951 : Int)/10^30,(-115529433986505747438607751 : Int)/10^30)
theorem v1270_pa_checked : Scalar.distance (sourceCoefficient 14 18 1 0) v1270_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1270_pb : Scalar.QComplex := ((-49848353750554897345456 : Int)/10^30,(-431477517874043466281043439 : Int)/10^30)
theorem v1270_pb_checked : Scalar.distance (sourceCoefficient 14 18 1 1) v1270_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1270_pg : Scalar.QComplex := ((-93086429249103325015918 : Int)/10^30,(10754222554742394305 : Int)/10^30)
theorem v1270_pg_checked : Scalar.distance (sourceCoefficient 14 18 1 2) v1270_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1270_mb : Scalar.QComplex := ((-422194000089016913075564 : Int)/10^30,(-431477314198359864827433701 : Int)/10^30)
theorem v1270_mb_checked : Scalar.distance (sourceCoefficient 14 18 3 1) v1270_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1270_mg : Scalar.QComplex := ((-93086385308361743054540 : Int)/10^30,(91083614535287959426 : Int)/10^30)
theorem v1270_mg_checked : Scalar.distance (sourceCoefficient 14 18 3 2) v1270_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1270_upper : Scalar.QComplex := ((999998304550630797908361714816 : Int)/10^30,(-1841438531109746206833303811 : Int)/10^30)
theorem v1270_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 18 5) 1) 14) v1270_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1270 : Material (14 : Basis) (18 : Basis) where
  plus := ![v1270_pa,v1270_pb,v1270_pg]
  minus := ![(Primitive.Addresses.material1270 1).one,v1270_mb,v1270_mg]
  upper := v1270_upper
  lower := (Primitive.Addresses.material1270 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1270_pa_checked.trans (by decide +kernel)
    · exact v1270_pb_checked.trans (by decide +kernel)
    · exact v1270_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 18 Primitive.Addresses.material1270
    · exact v1270_mb_checked.trans (by decide +kernel)
    · exact v1270_mg_checked.trans (by decide +kernel)
  upper_error := v1270_upper_checked
  lower_error := reuse_lower_error 14 18 Primitive.Addresses.material1270

def v1271_pa : Scalar.QComplex := ((999999991395761352878057744475 : Int)/10^30,(-131181085603874165432308069 : Int)/10^30)
theorem v1271_pa_checked : Scalar.distance (sourceCoefficient 14 19 1 0) v1271_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1271_pb : Scalar.QComplex := ((-56601689566492516976152 : Int)/10^30,(-431477516891402039403305120 : Int)/10^30)
theorem v1271_pb_checked : Scalar.distance (sourceCoefficient 14 19 1 1) v1271_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1271_pg : Scalar.QComplex := ((-93086429053244781987699 : Int)/10^30,(12211178923260560548 : Int)/10^30)
theorem v1271_pg_checked : Scalar.distance (sourceCoefficient 14 19 1 2) v1271_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1271_mb : Scalar.QComplex := ((-428947332542403670870137 : Int)/10^30,(-431477307387894153632080515 : Int)/10^30)
theorem v1271_mb_checked : Scalar.distance (sourceCoefficient 14 19 3 1) v1271_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1271_mg : Scalar.QComplex := ((-93086383855215545801180 : Int)/10^30,(92540570192297581982 : Int)/10^30)
theorem v1271_mg_checked : Scalar.distance (sourceCoefficient 14 19 3 2) v1271_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1271_upper : Scalar.QComplex := ((999998275606589322411777381963 : Int)/10^30,(-1857090156083581650557103095 : Int)/10^30)
theorem v1271_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 19 5) 1) 14) v1271_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1271 : Material (14 : Basis) (19 : Basis) where
  plus := ![v1271_pa,v1271_pb,v1271_pg]
  minus := ![(Primitive.Addresses.material1271 1).one,v1271_mb,v1271_mg]
  upper := v1271_upper
  lower := (Primitive.Addresses.material1271 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1271_pa_checked.trans (by decide +kernel)
    · exact v1271_pb_checked.trans (by decide +kernel)
    · exact v1271_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 19 Primitive.Addresses.material1271
    · exact v1271_mb_checked.trans (by decide +kernel)
    · exact v1271_mg_checked.trans (by decide +kernel)
  upper_error := v1271_upper_checked
  lower_error := reuse_lower_error 14 19 Primitive.Addresses.material1271

def v1272_pa : Scalar.QComplex := ((999999991023806365563929156038 : Int)/10^30,(-133986518681172135024201029 : Int)/10^30)
theorem v1272_pa_checked : Scalar.distance (sourceCoefficient 14 20 1 0) v1272_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1272_pb : Scalar.QComplex := ((-57812170870814038624042 : Int)/10^30,(-431477516700376803543582816 : Int)/10^30)
theorem v1272_pb_checked : Scalar.distance (sourceCoefficient 14 20 1 1) v1272_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1272_pg : Scalar.QComplex := ((-93086429015327026328619 : Int)/10^30,(12472326672179737765 : Int)/10^30)
theorem v1272_pg_checked : Scalar.distance (sourceCoefficient 14 20 1 2) v1272_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1272_mb : Scalar.QComplex := ((-430157813231161506100876 : Int)/10^30,(-431477306152278141324451966 : Int)/10^30)
theorem v1272_mb_checked : Scalar.distance (sourceCoefficient 14 20 3 1) v1272_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1272_mg : Scalar.QComplex := ((-93086383591939058601361 : Int)/10^30,(92801717811258201853 : Int)/10^30)
theorem v1272_mg_checked : Scalar.distance (sourceCoefficient 14 20 3 2) v1272_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1272_upper : Scalar.QComplex := ((999998270392711904565287647647 : Int)/10^30,(-1859895584340556036221180297 : Int)/10^30)
theorem v1272_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 20 5) 1) 14) v1272_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1272 : Material (14 : Basis) (20 : Basis) where
  plus := ![v1272_pa,v1272_pb,v1272_pg]
  minus := ![(Primitive.Addresses.material1272 1).one,v1272_mb,v1272_mg]
  upper := v1272_upper
  lower := (Primitive.Addresses.material1272 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1272_pa_checked.trans (by decide +kernel)
    · exact v1272_pb_checked.trans (by decide +kernel)
    · exact v1272_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 20 Primitive.Addresses.material1272
    · exact v1272_mb_checked.trans (by decide +kernel)
    · exact v1272_mg_checked.trans (by decide +kernel)
  upper_error := v1272_upper_checked
  lower_error := reuse_lower_error 14 20 Primitive.Addresses.material1272

def v1273_pa : Scalar.QComplex := ((999999982516371128550930210235 : Int)/10^30,(-186995340683186170837786401 : Int)/10^30)
theorem v1273_pa_checked : Scalar.distance (sourceCoefficient 14 21 1 0) v1273_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1273_pb : Scalar.QComplex := ((-80684285809084799303871 : Int)/10^30,(-431477512239883737584728181 : Int)/10^30)
theorem v1273_pb_checked : Scalar.distance (sourceCoefficient 14 21 1 1) v1273_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1273_pg : Scalar.QComplex := ((-93086428138212995163067 : Int)/10^30,(17406728647018849950 : Int)/10^30)
theorem v1273_pg_checked : Scalar.distance (sourceCoefficient 14 21 1 2) v1273_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1273_mb : Scalar.QComplex := ((-453029915803893945198288 : Int)/10^30,(-431477281954181666300254313 : Int)/10^30)
theorem v1273_mb_checked : Scalar.distance (sourceCoefficient 14 21 3 1) v1273_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1273_mg : Scalar.QComplex := ((-93086378456658686954410 : Int)/10^30,(97736117191884040348 : Int)/10^30)
theorem v1273_mg_checked : Scalar.distance (sourceCoefficient 14 21 3 2) v1273_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1273_upper : Scalar.QComplex := ((999998170396871485668274454116 : Int)/10^30,(-1912904312709095123091212083 : Int)/10^30)
theorem v1273_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 21 5) 1) 14) v1273_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1273 : Material (14 : Basis) (21 : Basis) where
  plus := ![v1273_pa,v1273_pb,v1273_pg]
  minus := ![(Primitive.Addresses.material1273 1).one,v1273_mb,v1273_mg]
  upper := v1273_upper
  lower := (Primitive.Addresses.material1273 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1273_pa_checked.trans (by decide +kernel)
    · exact v1273_pb_checked.trans (by decide +kernel)
    · exact v1273_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 21 Primitive.Addresses.material1273
    · exact v1273_mb_checked.trans (by decide +kernel)
    · exact v1273_mg_checked.trans (by decide +kernel)
  upper_error := v1273_upper_checked
  lower_error := reuse_lower_error 14 21 Primitive.Addresses.material1273

def v1274_pa : Scalar.QComplex := ((999999982254709527175478226517 : Int)/10^30,(-188389438745259044264039305 : Int)/10^30)
theorem v1274_pa_checked : Scalar.distance (sourceCoefficient 14 22 1 0) v1274_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1274_pb : Scalar.QComplex := ((-81285807778303024733348 : Int)/10^30,(-431477512100759258592534619 : Int)/10^30)
theorem v1274_pb_checked : Scalar.distance (sourceCoefficient 14 22 1 1) v1274_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1274_pg : Scalar.QComplex := ((-93086428111027151006201 : Int)/10^30,(17536500257827599981 : Int)/10^30)
theorem v1274_pg_checked : Scalar.distance (sourceCoefficient 14 22 1 2) v1274_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1274_mb : Scalar.QComplex := ((-453631437429079891139416 : Int)/10^30,(-431477281295970871218942247 : Int)/10^30)
theorem v1274_mb_checked : Scalar.distance (sourceCoefficient 14 22 3 1) v1274_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1274_mg : Scalar.QComplex := ((-93086378317485797488510 : Int)/10^30,(97865888730912729717 : Int)/10^30)
theorem v1274_mg_checked : Scalar.distance (sourceCoefficient 14 22 3 2) v1274_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1274_upper : Scalar.QComplex := ((999998167729123490457510674903 : Int)/10^30,(-1914298408243218509102980071 : Int)/10^30)
theorem v1274_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 22 5) 1) 14) v1274_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1274 : Material (14 : Basis) (22 : Basis) where
  plus := ![v1274_pa,v1274_pb,v1274_pg]
  minus := ![(Primitive.Addresses.material1274 1).one,v1274_mb,v1274_mg]
  upper := v1274_upper
  lower := (Primitive.Addresses.material1274 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1274_pa_checked.trans (by decide +kernel)
    · exact v1274_pb_checked.trans (by decide +kernel)
    · exact v1274_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 22 Primitive.Addresses.material1274
    · exact v1274_mb_checked.trans (by decide +kernel)
    · exact v1274_mg_checked.trans (by decide +kernel)
  upper_error := v1274_upper_checked
  lower_error := reuse_lower_error 14 22 Primitive.Addresses.material1274

def v1275_pa : Scalar.QComplex := ((999999980259515351795019876866 : Int)/10^30,(-198698185464093320441927161 : Int)/10^30)
theorem v1275_pa_checked : Scalar.distance (sourceCoefficient 14 23 1 0) v1275_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1275_pb : Scalar.QComplex := ((-85733800204099921396573 : Int)/10^30,(-431477511037291678542262605 : Int)/10^30)
theorem v1275_pb_checked : Scalar.distance (sourceCoefficient 14 23 1 1) v1275_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1275_pg : Scalar.QComplex := ((-93086427903448805711902 : Int)/10^30,(18496104680871492853 : Int)/10^30)
theorem v1275_pg_checked : Scalar.distance (sourceCoefficient 14 23 1 2) v1275_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1275_mb : Scalar.QComplex := ((-458079427280961299600608 : Int)/10^30,(-431477276394086553825784786 : Int)/10^30)
theorem v1275_mb_checked : Scalar.distance (sourceCoefficient 14 23 3 1) v1275_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1275_mg : Scalar.QComplex := ((-93086377281812131377087 : Int)/10^30,(98825492617521276794 : Int)/10^30)
theorem v1275_mg_checked : Scalar.distance (sourceCoefficient 14 23 3 2) v1275_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1275_upper : Scalar.QComplex := ((999998147941970652173377891449 : Int)/10^30,(-1924607136164861353926442365 : Int)/10^30)
theorem v1275_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 23 5) 1) 14) v1275_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1275 : Material (14 : Basis) (23 : Basis) where
  plus := ![v1275_pa,v1275_pb,v1275_pg]
  minus := ![(Primitive.Addresses.material1275 1).one,v1275_mb,v1275_mg]
  upper := v1275_upper
  lower := (Primitive.Addresses.material1275 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1275_pa_checked.trans (by decide +kernel)
    · exact v1275_pb_checked.trans (by decide +kernel)
    · exact v1275_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 23 Primitive.Addresses.material1275
    · exact v1275_mb_checked.trans (by decide +kernel)
    · exact v1275_mg_checked.trans (by decide +kernel)
  upper_error := v1275_upper_checked
  lower_error := reuse_lower_error 14 23 Primitive.Addresses.material1275

def v1276_pa : Scalar.QComplex := ((999999968838896068265010286174 : Int)/10^30,(-249644160541470669472244464 : Int)/10^30)
theorem v1276_pa_checked : Scalar.distance (sourceCoefficient 14 24 1 0) v1276_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1276_pb : Scalar.QComplex := ((-107715842855826637797229 : Int)/10^30,(-431477504883950219547115113 : Int)/10^30)
theorem v1276_pb_checked : Scalar.distance (sourceCoefficient 14 24 1 1) v1276_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1276_pg : Scalar.QComplex := ((-93086426708139308115382 : Int)/10^30,(23238483577495374500 : Int)/10^30)
theorem v1276_pg_checked : Scalar.distance (sourceCoefficient 14 24 1 2) v1276_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1276_mb : Scalar.QComplex := ((-480061456437712364883265 : Int)/10^30,(-431477251271234612009955304 : Int)/10^30)
theorem v1276_mb_checked : Scalar.distance (sourceCoefficient 14 24 3 1) v1276_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1276_mg : Scalar.QComplex := ((-93086371994043679879224 : Int)/10^30,(103567868716842496121 : Int)/10^30)
theorem v1276_mg_checked : Scalar.distance (sourceCoefficient 14 24 3 2) v1276_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1276_upper : Scalar.QComplex := ((999998048593237177516560593681 : Int)/10^30,(-1975553015653240546941682367 : Int)/10^30)
theorem v1276_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 24 5) 1) 14) v1276_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1276 : Material (14 : Basis) (24 : Basis) where
  plus := ![v1276_pa,v1276_pb,v1276_pg]
  minus := ![(Primitive.Addresses.material1276 1).one,v1276_mb,v1276_mg]
  upper := v1276_upper
  lower := (Primitive.Addresses.material1276 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1276_pa_checked.trans (by decide +kernel)
    · exact v1276_pb_checked.trans (by decide +kernel)
    · exact v1276_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 24 Primitive.Addresses.material1276
    · exact v1276_mb_checked.trans (by decide +kernel)
    · exact v1276_mg_checked.trans (by decide +kernel)
  upper_error := v1276_upper_checked
  lower_error := reuse_lower_error 14 24 Primitive.Addresses.material1276

def v1277_pa : Scalar.QComplex := ((999999962836850111875547148628 : Int)/10^30,(-272628498868238637586780966 : Int)/10^30)
theorem v1277_pa_checked : Scalar.distance (sourceCoefficient 14 25 1 0) v1277_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1277_pb : Scalar.QComplex := ((-117633067933441402528959 : Int)/10^30,(-431477501619073692594885404 : Int)/10^30)
theorem v1277_pb_checked : Scalar.distance (sourceCoefficient 14 25 1 1) v1277_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1277_pg : Scalar.QComplex := ((-93086426076604569665538 : Int)/10^30,(25378013549400889922 : Int)/10^30)
theorem v1277_pg_checked : Scalar.distance (sourceCoefficient 14 25 1 2) v1277_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1277_mb : Scalar.QComplex := ((-489978675005249595462930 : Int)/10^30,(-431477239448240713975800841 : Int)/10^30)
theorem v1277_mb_checked : Scalar.distance (sourceCoefficient 14 25 3 1) v1277_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1277_mg : Scalar.QComplex := ((-93086369516191171677019 : Int)/10^30,(105707397347117185638 : Int)/10^30)
theorem v1277_mg_checked : Scalar.distance (sourceCoefficient 14 25 3 2) v1277_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1277_upper : Scalar.QComplex := ((999998002922317331352904964511 : Int)/10^30,(-1998537309388549688002472593 : Int)/10^30)
theorem v1277_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 25 5) 1) 14) v1277_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1277 : Material (14 : Basis) (25 : Basis) where
  plus := ![v1277_pa,v1277_pb,v1277_pg]
  minus := ![(Primitive.Addresses.material1277 1).one,v1277_mb,v1277_mg]
  upper := v1277_upper
  lower := (Primitive.Addresses.material1277 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1277_pa_checked.trans (by decide +kernel)
    · exact v1277_pb_checked.trans (by decide +kernel)
    · exact v1277_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 25 Primitive.Addresses.material1277
    · exact v1277_mb_checked.trans (by decide +kernel)
    · exact v1277_mg_checked.trans (by decide +kernel)
  upper_error := v1277_upper_checked
  lower_error := reuse_lower_error 14 25 Primitive.Addresses.material1277

def v1278_pa : Scalar.QComplex := ((999999960807718603707688610102 : Int)/10^30,(-279972429457883766340395628 : Int)/10^30)
theorem v1278_pa_checked : Scalar.distance (sourceCoefficient 14 26 1 0) v1278_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1278_pb : Scalar.QComplex := ((-120801808809206793133519 : Int)/10^30,(-431477500511815633376143443 : Int)/10^30)
theorem v1278_pb_checked : Scalar.distance (sourceCoefficient 14 26 1 1) v1278_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1278_pg : Scalar.QComplex := ((-93086425862723019730692 : Int)/10^30,(26061633819752633968 : Int)/10^30)
theorem v1278_pg_checked : Scalar.distance (sourceCoefficient 14 26 1 2) v1278_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1278_mb : Scalar.QComplex := ((-493147413745634103353815 : Int)/10^30,(-431477235606502406045528826 : Int)/10^30)
theorem v1278_mb_checked : Scalar.distance (sourceCoefficient 14 26 3 1) v1278_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1278_mg : Scalar.QComplex := ((-93086368712376197180524 : Int)/10^30,(106391017178355715317 : Int)/10^30)
theorem v1278_mg_checked : Scalar.distance (sourceCoefficient 14 26 3 2) v1278_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1278_upper : Scalar.QComplex := ((999997988218230883789318266736 : Int)/10^30,(-2005881225538175980441332625 : Int)/10^30)
theorem v1278_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 26 5) 1) 14) v1278_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1278 : Material (14 : Basis) (26 : Basis) where
  plus := ![v1278_pa,v1278_pb,v1278_pg]
  minus := ![(Primitive.Addresses.material1278 1).one,v1278_mb,v1278_mg]
  upper := v1278_upper
  lower := (Primitive.Addresses.material1278 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1278_pa_checked.trans (by decide +kernel)
    · exact v1278_pb_checked.trans (by decide +kernel)
    · exact v1278_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 26 Primitive.Addresses.material1278
    · exact v1278_mb_checked.trans (by decide +kernel)
    · exact v1278_mg_checked.trans (by decide +kernel)
  upper_error := v1278_upper_checked
  lower_error := reuse_lower_error 14 26 Primitive.Addresses.material1278

def v1279_pa : Scalar.QComplex := ((999999959382465139093986362753 : Int)/10^30,(-285017662736939671750058433 : Int)/10^30)
theorem v1279_pa_checked : Scalar.distance (sourceCoefficient 14 27 1 0) v1279_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1279_pb : Scalar.QComplex := ((-122978713492614935391123 : Int)/10^30,(-431477499733156417283974027 : Int)/10^30)
theorem v1279_pb_checked : Scalar.distance (sourceCoefficient 14 27 1 1) v1279_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1279_pg : Scalar.QComplex := ((-93086425712393650530243 : Int)/10^30,(26531276566717253560 : Int)/10^30)
theorem v1279_pg_checked : Scalar.distance (sourceCoefficient 14 27 1 2) v1279_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1279_mb : Scalar.QComplex := ((-495324316946533308541366 : Int)/10^30,(-431477232949272782249916149 : Int)/10^30)
theorem v1279_mb_checked : Scalar.distance (sourceCoefficient 14 27 3 1) v1279_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1279_mg : Scalar.QComplex := ((-93086368156766345248230 : Int)/10^30,(106860659620723401443 : Int)/10^30)
theorem v1279_mg_checked : Scalar.distance (sourceCoefficient 14 27 3 2) v1279_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1279_upper : Scalar.QComplex := ((999997978085364602260456649170 : Int)/10^30,(-2010926448843091389490945795 : Int)/10^30)
theorem v1279_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 27 5) 1) 14) v1279_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1279 : Material (14 : Basis) (27 : Basis) where
  plus := ![v1279_pa,v1279_pb,v1279_pg]
  minus := ![(Primitive.Addresses.material1279 1).one,v1279_mb,v1279_mg]
  upper := v1279_upper
  lower := (Primitive.Addresses.material1279 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1279_pa_checked.trans (by decide +kernel)
    · exact v1279_pb_checked.trans (by decide +kernel)
    · exact v1279_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 27 Primitive.Addresses.material1279
    · exact v1279_mb_checked.trans (by decide +kernel)
    · exact v1279_mg_checked.trans (by decide +kernel)
  upper_error := v1279_upper_checked
  lower_error := reuse_lower_error 14 27 Primitive.Addresses.material1279

def v1280_pa : Scalar.QComplex := ((999999957422221715502116996538 : Int)/10^30,(-291814247006770665592310466 : Int)/10^30)
theorem v1280_pa_checked : Scalar.distance (sourceCoefficient 14 28 1 0) v1280_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1280_pb : Scalar.QComplex := ((-125911286733162060499328 : Int)/10^30,(-431477498661050022704590934 : Int)/10^30)
theorem v1280_pb_checked : Scalar.distance (sourceCoefficient 14 28 1 1) v1280_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1280_pg : Scalar.QComplex := ((-93086425505510161970143 : Int)/10^30,(27163946322022783156 : Int)/10^30)
theorem v1280_pg_checked : Scalar.distance (sourceCoefficient 14 28 1 2) v1280_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1280_mb : Scalar.QComplex := ((-498256888169969858333351 : Int)/10^30,(-431477229346488158468353622 : Int)/10^30)
theorem v1280_mb_checked : Scalar.distance (sourceCoefficient 14 28 3 1) v1280_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1280_mg : Scalar.QComplex := ((-93086367403917429279653 : Int)/10^30,(107493328961925933761 : Int)/10^30)
theorem v1280_mg_checked : Scalar.distance (sourceCoefficient 14 28 3 2) v1280_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1280_upper : Scalar.QComplex := ((999997964394836229801095189351 : Int)/10^30,(-2017723019607006179066279919 : Int)/10^30)
theorem v1280_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 14 28 5) 1) 14) v1280_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1280 : Material (14 : Basis) (28 : Basis) where
  plus := ![v1280_pa,v1280_pb,v1280_pg]
  minus := ![(Primitive.Addresses.material1280 1).one,v1280_mb,v1280_mg]
  upper := v1280_upper
  lower := (Primitive.Addresses.material1280 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1280_pa_checked.trans (by decide +kernel)
    · exact v1280_pb_checked.trans (by decide +kernel)
    · exact v1280_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 14 28 Primitive.Addresses.material1280
    · exact v1280_mb_checked.trans (by decide +kernel)
    · exact v1280_mg_checked.trans (by decide +kernel)
  upper_error := v1280_upper_checked
  lower_error := reuse_lower_error 14 28 Primitive.Addresses.material1280

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
