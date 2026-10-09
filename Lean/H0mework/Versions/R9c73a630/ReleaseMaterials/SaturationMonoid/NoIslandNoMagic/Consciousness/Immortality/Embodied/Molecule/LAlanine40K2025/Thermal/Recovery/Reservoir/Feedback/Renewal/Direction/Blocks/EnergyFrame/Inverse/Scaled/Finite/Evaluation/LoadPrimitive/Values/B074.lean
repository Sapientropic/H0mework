import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B049
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B050

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1185_pa : Scalar.QComplex := ((999999997535450017066449262662 : Int)/10^30,(-70207549165264947712284883 : Int)/10^30)
theorem v1185_pa_checked : Scalar.distance (sourceCoefficient 13 16 1 0) v1185_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1185_pb : Scalar.QComplex := ((-30292979258713314673672 : Int)/10^30,(-431477519785609428014769963 : Int)/10^30)
theorem v1185_pb_checked : Scalar.distance (sourceCoefficient 13 16 1 1) v1185_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1185_pg : Scalar.QComplex := ((-93086429651202002814680 : Int)/10^30,(6535370102462487725 : Int)/10^30)
theorem v1185_pg_checked : Scalar.distance (sourceCoefficient 13 16 1 2) v1185_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1185_mb : Scalar.QComplex := ((-402638634528130309722818 : Int)/10^30,(-431477332985332559884619664 : Int)/10^30)
theorem v1185_mb_checked : Scalar.distance (sourceCoefficient 13 16 3 1) v1185_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1185_mg : Scalar.QComplex := ((-93086389351139927390201 : Int)/10^30,(86864764000872681000 : Int)/10^30)
theorem v1185_mg_checked : Scalar.distance (sourceCoefficient 13 16 3 2) v1185_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1185_upper : Scalar.QComplex := ((999998386981061259278440610979 : Int)/10^30,(-1796116721054438149604929629 : Int)/10^30)
theorem v1185_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 16 5) 1) 14) v1185_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1185 : Material (13 : Basis) (16 : Basis) where
  plus := ![v1185_pa,v1185_pb,v1185_pg]
  minus := ![(Primitive.Addresses.material1185 1).one,v1185_mb,v1185_mg]
  upper := v1185_upper
  lower := (Primitive.Addresses.material1185 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1185_pa_checked.trans (by decide +kernel)
    · exact v1185_pb_checked.trans (by decide +kernel)
    · exact v1185_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 16 Primitive.Addresses.material1185
    · exact v1185_mb_checked.trans (by decide +kernel)
    · exact v1185_mg_checked.trans (by decide +kernel)
  upper_error := v1185_upper_checked
  lower_error := reuse_lower_error 13 16 Primitive.Addresses.material1185

def v1186_pa : Scalar.QComplex := ((999999997043272476122957289690 : Int)/10^30,(-76898992444711834274756153 : Int)/10^30)
theorem v1186_pa_checked : Scalar.distance (sourceCoefficient 13 17 1 0) v1186_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1186_pb : Scalar.QComplex := ((-33180186612184690256567 : Int)/10^30,(-431477519525831497196858839 : Int)/10^30)
theorem v1186_pb_checked : Scalar.distance (sourceCoefficient 13 17 1 1) v1186_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1186_pg : Scalar.QComplex := ((-93086429600272392076687 : Int)/10^30,(7158252667701549415 : Int)/10^30)
theorem v1186_pg_checked : Scalar.distance (sourceCoefficient 13 17 1 2) v1186_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1186_mb : Scalar.QComplex := ((-405525840582385781381533 : Int)/10^30,(-431477330234024814740182038 : Int)/10^30)
theorem v1186_mb_checked : Scalar.distance (sourceCoefficient 13 17 3 1) v1186_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1186_mg : Scalar.QComplex := ((-93086388762690735403659 : Int)/10^30,(87487646290234136230 : Int)/10^30)
theorem v1186_mg_checked : Scalar.distance (sourceCoefficient 13 17 3 2) v1186_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1186_upper : Scalar.QComplex := ((999998374940060394042606227667 : Int)/10^30,(-1802808153518312517903874324 : Int)/10^30)
theorem v1186_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 17 5) 1) 14) v1186_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1186 : Material (13 : Basis) (17 : Basis) where
  plus := ![v1186_pa,v1186_pb,v1186_pg]
  minus := ![(Primitive.Addresses.material1186 1).one,v1186_mb,v1186_mg]
  upper := v1186_upper
  lower := (Primitive.Addresses.material1186 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1186_pa_checked.trans (by decide +kernel)
    · exact v1186_pb_checked.trans (by decide +kernel)
    · exact v1186_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 17 Primitive.Addresses.material1186
    · exact v1186_mb_checked.trans (by decide +kernel)
    · exact v1186_mg_checked.trans (by decide +kernel)
  upper_error := v1186_upper_checked
  lower_error := reuse_lower_error 13 17 Primitive.Addresses.material1186

def v1187_pa : Scalar.QComplex := ((999999995077784938283598194072 : Int)/10^30,(-99219101483558106741155193 : Int)/10^30)
theorem v1187_pa_checked : Scalar.distance (sourceCoefficient 13 18 1 0) v1187_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1187_pb : Scalar.QComplex := ((-42810811903974881794314 : Int)/10^30,(-431477518473044889834906702 : Int)/10^30)
theorem v1187_pb_checked : Scalar.distance (sourceCoefficient 13 18 1 1) v1187_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1187_pg : Scalar.QComplex := ((-93086429395228839169522 : Int)/10^30,(9235951930368618374 : Int)/10^30)
theorem v1187_pg_checked : Scalar.distance (sourceCoefficient 13 18 1 2) v1187_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1187_mb : Scalar.QComplex := ((-415156461379746609061810 : Int)/10^30,(-431477320870442719825550270 : Int)/10^30)
theorem v1187_mb_checked : Scalar.distance (sourceCoefficient 13 18 3 1) v1187_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1187_mg : Scalar.QComplex := ((-93086386764686371262982 : Int)/10^30,(89565344602335462810 : Int)/10^30)
theorem v1187_mg_checked : Scalar.distance (sourceCoefficient 13 18 3 2) v1187_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1187_upper : Scalar.QComplex := ((999998334452092446992016971991 : Int)/10^30,(-1825128225921725098521013293 : Int)/10^30)
theorem v1187_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 18 5) 1) 14) v1187_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1187 : Material (13 : Basis) (18 : Basis) where
  plus := ![v1187_pa,v1187_pb,v1187_pg]
  minus := ![(Primitive.Addresses.material1187 1).one,v1187_mb,v1187_mg]
  upper := v1187_upper
  lower := (Primitive.Addresses.material1187 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1187_pa_checked.trans (by decide +kernel)
    · exact v1187_pb_checked.trans (by decide +kernel)
    · exact v1187_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 18 Primitive.Addresses.material1187
    · exact v1187_mb_checked.trans (by decide +kernel)
    · exact v1187_mg_checked.trans (by decide +kernel)
  upper_error := v1187_upper_checked
  lower_error := reuse_lower_error 13 18 Primitive.Addresses.material1187

def v1188_pa : Scalar.QComplex := ((999999993402355015870330433049 : Int)/10^30,(-114870753130335224581941640 : Int)/10^30)
theorem v1188_pa_checked : Scalar.distance (sourceCoefficient 13 19 1 0) v1188_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1188_pb : Scalar.QComplex := ((-49564147728371963305019 : Int)/10^30,(-431477517563836231651783613 : Int)/10^30)
theorem v1188_pb_checked : Scalar.distance (sourceCoefficient 13 19 1 1) v1188_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1188_pg : Scalar.QComplex := ((-93086429219173165300891 : Int)/10^30,(10692908301168077012 : Int)/10^30)
theorem v1188_pg_checked : Scalar.distance (sourceCoefficient 13 19 1 2) v1188_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1188_mb : Scalar.QComplex := ((-421909793904961997680871 : Int)/10^30,(-431477314133409742682301882 : Int)/10^30)
theorem v1188_mb_checked : Scalar.distance (sourceCoefficient 13 19 3 1) v1188_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1188_mg : Scalar.QComplex := ((-93086385331343033827045 : Int)/10^30,(91022300278715361109 : Int)/10^30)
theorem v1188_mg_checked : Scalar.distance (sourceCoefficient 13 19 3 2) v1188_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1188_upper : Scalar.QComplex := ((999998305763334184343196246093 : Int)/10^30,(-1840779851365565608372313521 : Int)/10^30)
theorem v1188_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 19 5) 1) 14) v1188_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1188 : Material (13 : Basis) (19 : Basis) where
  plus := ![v1188_pa,v1188_pb,v1188_pg]
  minus := ![(Primitive.Addresses.material1188 1).one,v1188_mb,v1188_mg]
  upper := v1188_upper
  lower := (Primitive.Addresses.material1188 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1188_pa_checked.trans (by decide +kernel)
    · exact v1188_pb_checked.trans (by decide +kernel)
    · exact v1188_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 19 Primitive.Addresses.material1188
    · exact v1188_mb_checked.trans (by decide +kernel)
    · exact v1188_mg_checked.trans (by decide +kernel)
  upper_error := v1188_upper_checked
  lower_error := reuse_lower_error 13 19 Primitive.Addresses.material1188

def v1189_pa : Scalar.QComplex := ((999999993076157575173427488910 : Int)/10^30,(-117676186213326743326145128 : Int)/10^30)
theorem v1189_pa_checked : Scalar.distance (sourceCoefficient 13 20 1 0) v1189_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1189_pb : Scalar.QComplex := ((-50774629034331243924219 : Int)/10^30,(-431477517385973230888747678 : Int)/10^30)
theorem v1189_pb_checked : Scalar.distance (sourceCoefficient 13 20 1 1) v1189_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1189_pg : Scalar.QComplex := ((-93086429184804915184308 : Int)/10^30,(10954056050528914365 : Int)/10^30)
theorem v1189_pg_checked : Scalar.distance (sourceCoefficient 13 20 1 2) v1189_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1189_mb : Scalar.QComplex := ((-423120274606716007356484 : Int)/10^30,(-431477312910955959157145802 : Int)/10^30)
theorem v1189_mb_checked : Scalar.distance (sourceCoefficient 13 20 3 1) v1189_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1189_mg : Scalar.QComplex := ((-93086385071616050466948 : Int)/10^30,(91283447901180704371 : Int)/10^30)
theorem v1189_mg_checked : Scalar.distance (sourceCoefficient 13 20 3 2) v1189_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1189_upper : Scalar.QComplex := ((999998300595214235136892206577 : Int)/10^30,(-1843585279707206909077957501 : Int)/10^30)
theorem v1189_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 20 5) 1) 14) v1189_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1189 : Material (13 : Basis) (20 : Basis) where
  plus := ![v1189_pa,v1189_pb,v1189_pg]
  minus := ![(Primitive.Addresses.material1189 1).one,v1189_mb,v1189_mg]
  upper := v1189_upper
  lower := (Primitive.Addresses.material1189 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1189_pa_checked.trans (by decide +kernel)
    · exact v1189_pb_checked.trans (by decide +kernel)
    · exact v1189_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 20 Primitive.Addresses.material1189
    · exact v1189_mb_checked.trans (by decide +kernel)
    · exact v1189_mg_checked.trans (by decide +kernel)
  upper_error := v1189_upper_checked
  lower_error := reuse_lower_error 13 20 Primitive.Addresses.material1189

def v1190_pa : Scalar.QComplex := ((999999985433313856689735741696 : Int)/10^30,(-170685008347048989793112066 : Int)/10^30)
theorem v1190_pa_checked : Scalar.distance (sourceCoefficient 13 21 1 0) v1190_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1190_pb : Scalar.QComplex := ((-73646744010488092471585 : Int)/10^30,(-431477513174181366465096784 : Int)/10^30)
theorem v1190_pb_checked : Scalar.distance (sourceCoefficient 13 21 1 1) v1190_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1190_pg : Scalar.QComplex := ((-93086428374758998741777 : Int)/10^30,(15888458035584899135 : Int)/10^30)
theorem v1190_pg_checked : Scalar.distance (sourceCoefficient 13 21 1 2) v1190_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1190_mb : Scalar.QComplex := ((-445992377431952456053280 : Int)/10^30,(-431477288961560560371340848 : Int)/10^30)
theorem v1190_mb_checked : Scalar.distance (sourceCoefficient 13 21 3 1) v1190_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1190_mg : Scalar.QComplex := ((-93086380003403759753791 : Int)/10^30,(96217847349900174017 : Int)/10^30)
theorem v1190_mg_checked : Scalar.distance (sourceCoefficient 13 21 3 2) v1190_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1190_upper : Scalar.QComplex := ((999998201463963819745258304141 : Int)/10^30,(-1896594009699660536289187475 : Int)/10^30)
theorem v1190_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 21 5) 1) 14) v1190_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1190 : Material (13 : Basis) (21 : Basis) where
  plus := ![v1190_pa,v1190_pb,v1190_pg]
  minus := ![(Primitive.Addresses.material1190 1).one,v1190_mb,v1190_mg]
  upper := v1190_upper
  lower := (Primitive.Addresses.material1190 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1190_pa_checked.trans (by decide +kernel)
    · exact v1190_pb_checked.trans (by decide +kernel)
    · exact v1190_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 21 Primitive.Addresses.material1190
    · exact v1190_mb_checked.trans (by decide +kernel)
    · exact v1190_mg_checked.trans (by decide +kernel)
  upper_error := v1190_upper_checked
  lower_error := reuse_lower_error 13 21 Primitive.Addresses.material1190

def v1191_pa : Scalar.QComplex := ((999999985194390458413532685104 : Int)/10^30,(-172079106413204217138187139 : Int)/10^30)
theorem v1191_pa_checked : Scalar.distance (sourceCoefficient 13 22 1 0) v1191_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1191_pb : Scalar.QComplex := ((-74248265980880613857336 : Int)/10^30,(-431477513041597569756521151 : Int)/10^30)
theorem v1191_pb_checked : Scalar.distance (sourceCoefficient 13 22 1 1) v1191_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1191_pg : Scalar.QComplex := ((-93086428349337003039089 : Int)/10^30,(16018229646710325625 : Int)/10^30)
theorem v1191_pg_checked : Scalar.distance (sourceCoefficient 13 22 1 2) v1191_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1191_mb : Scalar.QComplex := ((-446593899063957011742805 : Int)/10^30,(-431477288309890444124887251 : Int)/10^30)
theorem v1191_mb_checked : Scalar.distance (sourceCoefficient 13 22 3 1) v1191_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1191_mg : Scalar.QComplex := ((-93086379865994717812030 : Int)/10^30,(96347618890767661502 : Int)/10^30)
theorem v1191_mg_checked : Scalar.distance (sourceCoefficient 13 22 3 2) v1191_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1191_upper : Scalar.QComplex := ((999998198818953986722088437055 : Int)/10^30,(-1897988105277110345895223160 : Int)/10^30)
theorem v1191_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 22 5) 1) 14) v1191_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1191 : Material (13 : Basis) (22 : Basis) where
  plus := ![v1191_pa,v1191_pb,v1191_pg]
  minus := ![(Primitive.Addresses.material1191 1).one,v1191_mb,v1191_mg]
  upper := v1191_upper
  lower := (Primitive.Addresses.material1191 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1191_pa_checked.trans (by decide +kernel)
    · exact v1191_pb_checked.trans (by decide +kernel)
    · exact v1191_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 22 Primitive.Addresses.material1191
    · exact v1191_mb_checked.trans (by decide +kernel)
    · exact v1191_mg_checked.trans (by decide +kernel)
  upper_error := v1191_upper_checked
  lower_error := reuse_lower_error 13 22 Primitive.Addresses.material1191

def v1192_pa : Scalar.QComplex := ((999999983367335370934985785619 : Int)/10^30,(-182387853163209571689989305 : Int)/10^30)
theorem v1192_pa_checked : Scalar.distance (sourceCoefficient 13 23 1 0) v1192_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1192_pb : Scalar.QComplex := ((-78696258415643923528574 : Int)/10^30,(-431477512026495480525376193 : Int)/10^30)
theorem v1192_pb_checked : Scalar.distance (sourceCoefficient 13 23 1 1) v1192_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1192_pg : Scalar.QComplex := ((-93086428154801547236034 : Int)/10^30,(16977834072172222161 : Int)/10^30)
theorem v1192_pg_checked : Scalar.distance (sourceCoefficient 13 23 1 2) v1192_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1192_mb : Scalar.QComplex := ((-451041888966542070149466 : Int)/10^30,(-431477283456371591804563608 : Int)/10^30)
theorem v1192_mb_checked : Scalar.distance (sourceCoefficient 13 23 3 1) v1192_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1192_mg : Scalar.QComplex := ((-93086378843363934248759 : Int)/10^30,(97307222791049637544 : Int)/10^30)
theorem v1192_mg_checked : Scalar.distance (sourceCoefficient 13 23 3 2) v1192_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1192_upper : Scalar.QComplex := ((999998179199939932117993223332 : Int)/10^30,(-1908296833520117034926738321 : Int)/10^30)
theorem v1192_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 23 5) 1) 14) v1192_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1192 : Material (13 : Basis) (23 : Basis) where
  plus := ![v1192_pa,v1192_pb,v1192_pg]
  minus := ![(Primitive.Addresses.material1192 1).one,v1192_mb,v1192_mg]
  upper := v1192_upper
  lower := (Primitive.Addresses.material1192 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1192_pa_checked.trans (by decide +kernel)
    · exact v1192_pb_checked.trans (by decide +kernel)
    · exact v1192_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 23 Primitive.Addresses.material1192
    · exact v1192_mb_checked.trans (by decide +kernel)
    · exact v1192_mg_checked.trans (by decide +kernel)
  upper_error := v1192_upper_checked
  lower_error := reuse_lower_error 13 23 Primitive.Addresses.material1192

def v1193_pa : Scalar.QComplex := ((999999972777661886885432948603 : Int)/10^30,(-233333828420084518524233517 : Int)/10^30)
theorem v1193_pa_checked : Scalar.distance (sourceCoefficient 13 24 1 0) v1193_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1193_pb : Scalar.QComplex := ((-100678301119003425131073 : Int)/10^30,(-431477506112176975069513188 : Int)/10^30)
theorem v1193_pb_checked : Scalar.distance (sourceCoefficient 13 24 1 1) v1193_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1193_pg : Scalar.QComplex := ((-93086427023950197739184 : Int)/10^30,(21720212982720095902 : Int)/10^30)
theorem v1193_pg_checked : Scalar.distance (sourceCoefficient 13 24 1 2) v1193_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1193_mb : Scalar.QComplex := ((-473023918381191945118920 : Int)/10^30,(-431477258572542469972080946 : Int)/10^30)
theorem v1193_mb_checked : Scalar.distance (sourceCoefficient 13 24 3 1) v1193_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1193_mg : Scalar.QComplex := ((-93086373620053594834075 : Int)/10^30,(102049598959919322502 : Int)/10^30)
theorem v1193_mg_checked : Scalar.distance (sourceCoefficient 13 24 3 2) v1193_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1193_upper : Scalar.QComplex := ((999998080682150709548904188710 : Int)/10^30,(-1959242714622130625494516291 : Int)/10^30)
theorem v1193_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 24 5) 1) 14) v1193_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1193 : Material (13 : Basis) (24 : Basis) where
  plus := ![v1193_pa,v1193_pb,v1193_pg]
  minus := ![(Primitive.Addresses.material1193 1).one,v1193_mb,v1193_mg]
  upper := v1193_upper
  lower := (Primitive.Addresses.material1193 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1193_pa_checked.trans (by decide +kernel)
    · exact v1193_pb_checked.trans (by decide +kernel)
    · exact v1193_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 24 Primitive.Addresses.material1193
    · exact v1193_mb_checked.trans (by decide +kernel)
    · exact v1193_mg_checked.trans (by decide +kernel)
  upper_error := v1193_upper_checked
  lower_error := reuse_lower_error 13 24 Primitive.Addresses.material1193

def v1194_pa : Scalar.QComplex := ((999999967150498133912737691230 : Int)/10^30,(-256318166841690625741731177 : Int)/10^30)
theorem v1194_pa_checked : Scalar.distance (sourceCoefficient 13 25 1 0) v1194_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1194_pb : Scalar.QComplex := ((-110595526223898539674480 : Int)/10^30,(-431477502955135942825973509 : Int)/10^30)
theorem v1194_pb_checked : Scalar.distance (sourceCoefficient 13 25 1 1) v1194_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1194_pg : Scalar.QComplex := ((-93086426421495830815791 : Int)/10^30,(23859742961982397788 : Int)/10^30)
theorem v1194_pg_checked : Scalar.distance (sourceCoefficient 13 25 1 2) v1194_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1194_mb : Scalar.QComplex := ((-482941137069066690555749 : Int)/10^30,(-431477246857384002952820283 : Int)/10^30)
theorem v1194_mb_checked : Scalar.distance (sourceCoefficient 13 25 3 1) v1194_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1194_mg : Scalar.QComplex := ((-93086371171281440981792 : Int)/10^30,(104189127622645846641 : Int)/10^30)
theorem v1194_mg_checked : Scalar.distance (sourceCoefficient 13 25 3 2) v1194_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1194_upper : Scalar.QComplex := ((999998035386112344776986764524 : Int)/10^30,(-1982227009099290438457511444 : Int)/10^30)
theorem v1194_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 25 5) 1) 14) v1194_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1194 : Material (13 : Basis) (25 : Basis) where
  plus := ![v1194_pa,v1194_pb,v1194_pg]
  minus := ![(Primitive.Addresses.material1194 1).one,v1194_mb,v1194_mg]
  upper := v1194_upper
  lower := (Primitive.Addresses.material1194 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1194_pa_checked.trans (by decide +kernel)
    · exact v1194_pb_checked.trans (by decide +kernel)
    · exact v1194_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 25 Primitive.Addresses.material1194
    · exact v1194_mb_checked.trans (by decide +kernel)
    · exact v1194_mg_checked.trans (by decide +kernel)
  upper_error := v1194_upper_checked
  lower_error := reuse_lower_error 13 25 Primitive.Addresses.material1194

def v1195_pa : Scalar.QComplex := ((999999965241148576496975240023 : Int)/10^30,(-263662097463454722549683638 : Int)/10^30)
theorem v1195_pa_checked : Scalar.distance (sourceCoefficient 13 26 1 0) v1195_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1195_pb : Scalar.QComplex := ((-113764267108903005315992 : Int)/10^30,(-431477501882333362662337112 : Int)/10^30)
theorem v1195_pb_checked : Scalar.distance (sourceCoefficient 13 26 1 1) v1195_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1195_pg : Scalar.QComplex := ((-93086426216906009314303 : Int)/10^30,(24543363234825675216 : Int)/10^30)
theorem v1195_pg_checked : Scalar.distance (sourceCoefficient 13 26 1 2) v1195_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1195_mb : Scalar.QComplex := ((-486109875848423796650842 : Int)/10^30,(-431477243050101153275398641 : Int)/10^30)
theorem v1195_mb_checked : Scalar.distance (sourceCoefficient 13 26 3 1) v1195_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1195_mg : Scalar.QComplex := ((-93086370376758189308840 : Int)/10^30,(104872747464394251927 : Int)/10^30)
theorem v1195_mg_checked : Scalar.distance (sourceCoefficient 13 26 3 2) v1195_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1195_upper : Scalar.QComplex := ((999998020801807614129926033393 : Int)/10^30,(-1989570925487768431577709638 : Int)/10^30)
theorem v1195_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 26 5) 1) 14) v1195_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1195 : Material (13 : Basis) (26 : Basis) where
  plus := ![v1195_pa,v1195_pb,v1195_pg]
  minus := ![(Primitive.Addresses.material1195 1).one,v1195_mb,v1195_mg]
  upper := v1195_upper
  lower := (Primitive.Addresses.material1195 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1195_pa_checked.trans (by decide +kernel)
    · exact v1195_pb_checked.trans (by decide +kernel)
    · exact v1195_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 26 Primitive.Addresses.material1195
    · exact v1195_mb_checked.trans (by decide +kernel)
    · exact v1195_mg_checked.trans (by decide +kernel)
  upper_error := v1195_upper_checked
  lower_error := reuse_lower_error 13 26 Primitive.Addresses.material1195

def v1196_pa : Scalar.QComplex := ((999999963898184544880820184607 : Int)/10^30,(-268707330765085901992228038 : Int)/10^30)
theorem v1196_pa_checked : Scalar.distance (sourceCoefficient 13 27 1 0) v1196_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1196_pb : Scalar.QComplex := ((-115941171798804963014903 : Int)/10^30,(-431477501127344839996776141 : Int)/10^30)
theorem v1196_pb_checked : Scalar.distance (sourceCoefficient 13 27 1 1) v1196_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1196_pg : Scalar.QComplex := ((-93086426072959998035615 : Int)/10^30,(25013005983541504520 : Int)/10^30)
theorem v1196_pg_checked : Scalar.distance (sourceCoefficient 13 27 1 2) v1196_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1196_mb : Scalar.QComplex := ((-488286779076243557200461 : Int)/10^30,(-431477240416542208488843188 : Int)/10^30)
theorem v1196_mb_checked : Scalar.distance (sourceCoefficient 13 27 3 1) v1196_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1196_mg : Scalar.QComplex := ((-93086369827531691410276 : Int)/10^30,(105342389914021697505 : Int)/10^30)
theorem v1196_mg_checked : Scalar.distance (sourceCoefficient 13 27 3 2) v1196_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1196_upper : Scalar.QComplex := ((999998010751230604075292585850 : Int)/10^30,(-1994616148957283177151705772 : Int)/10^30)
theorem v1196_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 27 5) 1) 14) v1196_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1196 : Material (13 : Basis) (27 : Basis) where
  plus := ![v1196_pa,v1196_pb,v1196_pg]
  minus := ![(Primitive.Addresses.material1196 1).one,v1196_mb,v1196_mg]
  upper := v1196_upper
  lower := (Primitive.Addresses.material1196 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1196_pa_checked.trans (by decide +kernel)
    · exact v1196_pb_checked.trans (by decide +kernel)
    · exact v1196_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 27 Primitive.Addresses.material1196
    · exact v1196_mb_checked.trans (by decide +kernel)
    · exact v1196_mg_checked.trans (by decide +kernel)
  upper_error := v1196_upper_checked
  lower_error := reuse_lower_error 13 27 Primitive.Addresses.material1196

def v1197_pa : Scalar.QComplex := ((999999962048795671510284427303 : Int)/10^30,(-275503915065985080753321868 : Int)/10^30)
theorem v1197_pa_checked : Scalar.distance (sourceCoefficient 13 28 1 0) v1197_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1197_pb : Scalar.QComplex := ((-118873745048288903623502 : Int)/10^30,(-431477500087125942717028224 : Int)/10^30)
theorem v1197_pb_checked : Scalar.distance (sourceCoefficient 13 28 1 1) v1197_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1197_pg : Scalar.QComplex := ((-93086425874675721372145 : Int)/10^30,(25645675741257056120 : Int)/10^30)
theorem v1197_pg_checked : Scalar.distance (sourceCoefficient 13 28 1 2) v1197_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1197_mb : Scalar.QComplex := ((-491219350336134393175276 : Int)/10^30,(-431477236845645062421673983 : Int)/10^30)
theorem v1197_mb_checked : Scalar.distance (sourceCoefficient 13 28 3 1) v1197_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1197_mg : Scalar.QComplex := ((-93086369083281982056709 : Int)/10^30,(105975059265054983503 : Int)/10^30)
theorem v1197_mg_checked : Scalar.distance (sourceCoefficient 13 28 3 2) v1197_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1197_upper : Scalar.QComplex := ((999997997171556563111565384270 : Int)/10^30,(-2001412719943591002409253721 : Int)/10^30)
theorem v1197_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 28 5) 1) 14) v1197_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1197 : Material (13 : Basis) (28 : Basis) where
  plus := ![v1197_pa,v1197_pb,v1197_pg]
  minus := ![(Primitive.Addresses.material1197 1).one,v1197_mb,v1197_mg]
  upper := v1197_upper
  lower := (Primitive.Addresses.material1197 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1197_pa_checked.trans (by decide +kernel)
    · exact v1197_pb_checked.trans (by decide +kernel)
    · exact v1197_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 28 Primitive.Addresses.material1197
    · exact v1197_mb_checked.trans (by decide +kernel)
    · exact v1197_mg_checked.trans (by decide +kernel)
  upper_error := v1197_upper_checked
  lower_error := reuse_lower_error 13 28 Primitive.Addresses.material1197

def v1198_pa : Scalar.QComplex := ((999999958161643357053060378711 : Int)/10^30,(-289269271675105153503133257 : Int)/10^30)
theorem v1198_pa_checked : Scalar.distance (sourceCoefficient 13 29 1 0) v1198_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1198_pb : Scalar.QComplex := ((-124813186783395083003598 : Int)/10^30,(-431477497898917089485689999 : Int)/10^30)
theorem v1198_pb_checked : Scalar.distance (sourceCoefficient 13 29 1 1) v1198_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1198_pg : Scalar.QComplex := ((-93086425457714412211381 : Int)/10^30,(26927043621575269274 : Int)/10^30)
theorem v1198_pg_checked : Scalar.distance (sourceCoefficient 13 29 1 2) v1198_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1198_mb : Scalar.QComplex := ((-497158787971389281607983 : Int)/10^30,(-431477229531966309089453758 : Int)/10^30)
theorem v1198_mb_checked : Scalar.distance (sourceCoefficient 13 29 3 1) v1198_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1198_mg : Scalar.QComplex := ((-93086367560558058102088 : Int)/10^30,(107256426308442542844 : Int)/10^30)
theorem v1198_mg_checked : Scalar.distance (sourceCoefficient 13 29 3 2) v1198_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1198_upper : Scalar.QComplex := ((999997969526653314166469982244 : Int)/10^30,(-2015178049341957143199671753 : Int)/10^30)
theorem v1198_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 29 5) 1) 14) v1198_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1198 : Material (13 : Basis) (29 : Basis) where
  plus := ![v1198_pa,v1198_pb,v1198_pg]
  minus := ![(Primitive.Addresses.material1198 1).one,v1198_mb,v1198_mg]
  upper := v1198_upper
  lower := (Primitive.Addresses.material1198 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1198_pa_checked.trans (by decide +kernel)
    · exact v1198_pb_checked.trans (by decide +kernel)
    · exact v1198_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 29 Primitive.Addresses.material1198
    · exact v1198_mb_checked.trans (by decide +kernel)
    · exact v1198_mg_checked.trans (by decide +kernel)
  upper_error := v1198_upper_checked
  lower_error := reuse_lower_error 13 29 Primitive.Addresses.material1198

def v1199_pa : Scalar.QComplex := ((999999956639123865988874595352 : Int)/10^30,(-294485569065542958228870348 : Int)/10^30)
theorem v1199_pa_checked : Scalar.distance (sourceCoefficient 13 30 1 0) v1199_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1199_pb : Scalar.QComplex := ((-127063901764764038704317 : Int)/10^30,(-431477497041227244697194596 : Int)/10^30)
theorem v1199_pb_checked : Scalar.distance (sourceCoefficient 13 30 1 1) v1199_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1199_pg : Scalar.QComplex := ((-93086425294332984115108 : Int)/10^30,(27412610113713592638 : Int)/10^30)
theorem v1199_pg_checked : Scalar.distance (sourceCoefficient 13 30 1 2) v1199_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1199_mb : Scalar.QComplex := ((-499409501374566479853033 : Int)/10^30,(-431477226732011123176464655 : Int)/10^30)
theorem v1199_mb_checked : Scalar.distance (sourceCoefficient 13 30 3 1) v1199_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1199_mg : Scalar.QComplex := ((-93086366978154677227801 : Int)/10^30,(107741992478791455679 : Int)/10^30)
theorem v1199_mg_checked : Scalar.distance (sourceCoefficient 13 30 3 2) v1199_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1199_upper : Scalar.QComplex := ((999997959001280013623245573201 : Int)/10^30,(-2020394336335602214515568345 : Int)/10^30)
theorem v1199_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 30 5) 1) 14) v1199_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1199 : Material (13 : Basis) (30 : Basis) where
  plus := ![v1199_pa,v1199_pb,v1199_pg]
  minus := ![(Primitive.Addresses.material1199 1).one,v1199_mb,v1199_mg]
  upper := v1199_upper
  lower := (Primitive.Addresses.material1199 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1199_pa_checked.trans (by decide +kernel)
    · exact v1199_pb_checked.trans (by decide +kernel)
    · exact v1199_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 30 Primitive.Addresses.material1199
    · exact v1199_mb_checked.trans (by decide +kernel)
    · exact v1199_mg_checked.trans (by decide +kernel)
  upper_error := v1199_upper_checked
  lower_error := reuse_lower_error 13 30 Primitive.Addresses.material1199

def v1200_pa : Scalar.QComplex := ((999999953310235733112797834180 : Int)/10^30,(-305580638054573603303956930 : Int)/10^30)
theorem v1200_pa_checked : Scalar.distance (sourceCoefficient 13 31 1 0) v1200_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1200_pb : Scalar.QComplex := ((-131851174434768051702828 : Int)/10^30,(-431477495164862236381518515 : Int)/10^30)
theorem v1200_pb_checked : Scalar.distance (sourceCoefficient 13 31 1 1) v1200_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1200_pg : Scalar.QComplex := ((-93086424936993488538111 : Int)/10^30,(28445410454575150256 : Int)/10^30)
theorem v1200_pg_checked : Scalar.distance (sourceCoefficient 13 31 1 2) v1200_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1200_mb : Scalar.QComplex := ((-504196770642831594806075 : Int)/10^30,(-431477220724446110060981518 : Int)/10^30)
theorem v1200_mb_checked : Scalar.distance (sourceCoefficient 13 31 3 1) v1200_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1200_mg : Scalar.QComplex := ((-93086365729555136141717 : Int)/10^30,(108774792126726354377 : Int)/10^30)
theorem v1200_mg_checked : Scalar.distance (sourceCoefficient 13 31 3 2) v1200_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1200_upper : Scalar.QComplex := ((999997936523314300464161560364 : Int)/10^30,(-2031489383054471995814337186 : Int)/10^30)
theorem v1200_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 13 31 5) 1) 14) v1200_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1200 : Material (13 : Basis) (31 : Basis) where
  plus := ![v1200_pa,v1200_pb,v1200_pg]
  minus := ![(Primitive.Addresses.material1200 1).one,v1200_mb,v1200_mg]
  upper := v1200_upper
  lower := (Primitive.Addresses.material1200 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1200_pa_checked.trans (by decide +kernel)
    · exact v1200_pb_checked.trans (by decide +kernel)
    · exact v1200_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 13 31 Primitive.Addresses.material1200
    · exact v1200_mb_checked.trans (by decide +kernel)
    · exact v1200_mg_checked.trans (by decide +kernel)
  upper_error := v1200_upper_checked
  lower_error := reuse_lower_error 13 31 Primitive.Addresses.material1200

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
