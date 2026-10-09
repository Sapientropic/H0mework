import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B056
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B057

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1361_pa : Scalar.QComplex := ((999999951547448428859107656721 : Int)/10^30,(-311295841274232301512321461 : Int)/10^30)
theorem v1361_pa_checked : Scalar.distance (sourceCoefficient 15 27 1 0) v1361_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1361_pb : Scalar.QComplex := ((-134317156978888752571202 : Int)/10^30,(-431477497165002953136893900 : Int)/10^30)
theorem v1361_pb_checked : Scalar.distance (sourceCoefficient 15 27 1 1) v1361_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1361_pg : Scalar.QComplex := ((-93086425070701647521974 : Int)/10^30,(28977418407624718206 : Int)/10^30)
theorem v1361_pg_checked : Scalar.distance (sourceCoefficient 15 27 1 2) v1361_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1361_mb : Scalar.QComplex := ((-506662753994785649094549 : Int)/10^30,(-431477220596554210227299967 : Int)/10^30)
theorem v1361_mb_checked : Scalar.distance (sourceCoefficient 15 27 3 1) v1361_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1361_mg : Scalar.QComplex := ((-93086365404164342606885 : Int)/10^30,(109306799997069166653 : Int)/10^30)
theorem v1361_mg_checked : Scalar.distance (sourceCoefficient 15 27 3 2) v1361_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1361_upper : Scalar.QComplex := ((999997924896607343730126719867 : Int)/10^30,(-2037204574719595884944518937 : Int)/10^30)
theorem v1361_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 27 5) 1) 14) v1361_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1361 : Material (15 : Basis) (27 : Basis) where
  plus := ![v1361_pa,v1361_pb,v1361_pg]
  minus := ![(Primitive.Addresses.material1361 1).one,v1361_mb,v1361_mg]
  upper := v1361_upper
  lower := (Primitive.Addresses.material1361 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1361_pa_checked.trans (by decide +kernel)
    · exact v1361_pb_checked.trans (by decide +kernel)
    · exact v1361_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 27 Primitive.Addresses.material1361
    · exact v1361_mb_checked.trans (by decide +kernel)
    · exact v1361_mg_checked.trans (by decide +kernel)
  upper_error := v1361_upper_checked
  lower_error := reuse_lower_error 15 27 Primitive.Addresses.material1361

def v1362_pa : Scalar.QComplex := ((999999949408603143134472064278 : Int)/10^30,(-318092425490205000484182240 : Int)/10^30)
theorem v1362_pa_checked : Scalar.distance (sourceCoefficient 15 28 1 0) v1362_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1362_pb : Scalar.QComplex := ((-137249730203943448812068 : Int)/10^30,(-431477496041521433308867623 : Int)/10^30)
theorem v1362_pb_checked : Scalar.distance (sourceCoefficient 15 28 1 1) v1362_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1362_pg : Scalar.QComplex := ((-93086424849963650911086 : Int)/10^30,(29610088158752350825 : Int)/10^30)
theorem v1362_pg_checked : Scalar.distance (sourceCoefficient 15 28 1 2) v1362_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1362_mb : Scalar.QComplex := ((-509595325158395356547902 : Int)/10^30,(-431477216942394493695669703 : Int)/10^30)
theorem v1362_mb_checked : Scalar.distance (sourceCoefficient 15 28 3 1) v1362_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1362_mg : Scalar.QComplex := ((-93086364637460927351524 : Int)/10^30,(109939469322137987087 : Int)/10^30)
theorem v1362_mg_checked : Scalar.distance (sourceCoefficient 15 28 3 2) v1362_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1362_upper : Scalar.QComplex := ((999997911027477468099023592033 : Int)/10^30,(-2044001145121401848458275522 : Int)/10^30)
theorem v1362_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 28 5) 1) 14) v1362_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1362 : Material (15 : Basis) (28 : Basis) where
  plus := ![v1362_pa,v1362_pb,v1362_pg]
  minus := ![(Primitive.Addresses.material1362 1).one,v1362_mb,v1362_mg]
  upper := v1362_upper
  lower := (Primitive.Addresses.material1362 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1362_pa_checked.trans (by decide +kernel)
    · exact v1362_pb_checked.trans (by decide +kernel)
    · exact v1362_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 28 Primitive.Addresses.material1362
    · exact v1362_mb_checked.trans (by decide +kernel)
    · exact v1362_mg_checked.trans (by decide +kernel)
  upper_error := v1362_upper_checked
  lower_error := reuse_lower_error 15 28 Primitive.Addresses.material1362

def v1363_pa : Scalar.QComplex := ((999999944935204773073810504766 : Int)/10^30,(-331857781921293365362393896 : Int)/10^30)
theorem v1363_pa_checked : Scalar.distance (sourceCoefficient 15 29 1 0) v1363_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1363_pb : Scalar.QComplex := ((-143189171887838508815618 : Int)/10^30,(-431477493684677918893715260 : Int)/10^30)
theorem v1363_pb_checked : Scalar.distance (sourceCoefficient 15 29 1 1) v1363_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1363_pg : Scalar.QComplex := ((-93086424387526048300920 : Int)/10^30,(30891456025260283955 : Int)/10^30)
theorem v1363_pg_checked : Scalar.distance (sourceCoefficient 15 29 1 2) v1363_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1363_mb : Scalar.QComplex := ((-515534762596915027093871 : Int)/10^30,(-431477209460081186162916242 : Int)/10^30)
theorem v1363_mb_checked : Scalar.distance (sourceCoefficient 15 29 3 1) v1363_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1363_mg : Scalar.QComplex := ((-93086363069260738798052 : Int)/10^30,(111220836312471278475 : Int)/10^30)
theorem v1363_mg_checked : Scalar.distance (sourceCoefficient 15 29 3 2) v1363_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1363_upper : Scalar.QComplex := ((999997882796329343961702077200 : Int)/10^30,(-2057766473329929038389591568 : Int)/10^30)
theorem v1363_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 29 5) 1) 14) v1363_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1363 : Material (15 : Basis) (29 : Basis) where
  plus := ![v1363_pa,v1363_pb,v1363_pg]
  minus := ![(Primitive.Addresses.material1363 1).one,v1363_mb,v1363_mg]
  upper := v1363_upper
  lower := (Primitive.Addresses.material1363 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1363_pa_checked.trans (by decide +kernel)
    · exact v1363_pb_checked.trans (by decide +kernel)
    · exact v1363_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 29 Primitive.Addresses.material1363
    · exact v1363_mb_checked.trans (by decide +kernel)
    · exact v1363_mg_checked.trans (by decide +kernel)
  upper_error := v1363_upper_checked
  lower_error := reuse_lower_error 15 29 Primitive.Addresses.material1363

def v1364_pa : Scalar.QComplex := ((999999943190530937867564902759 : Int)/10^30,(-337074079242158718491163060 : Int)/10^30)
theorem v1364_pa_checked : Scalar.distance (sourceCoefficient 15 30 1 0) v1364_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1364_pb : Scalar.QComplex := ((-145439886849194832131771 : Int)/10^30,(-431477492763085004430455137 : Int)/10^30)
theorem v1364_pb_checked : Scalar.distance (sourceCoefficient 15 30 1 1) v1364_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1364_pg : Scalar.QComplex := ((-93086424206911657959649 : Int)/10^30,(31377022512001731393 : Int)/10^30)
theorem v1364_pg_checked : Scalar.distance (sourceCoefficient 15 30 1 2) v1364_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1364_mb : Scalar.QComplex := ((-517785475924934129364070 : Int)/10^30,(-431477206596222971639196186 : Int)/10^30)
theorem v1364_mb_checked : Scalar.distance (sourceCoefficient 15 30 3 1) v1364_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1364_mg : Scalar.QComplex := ((-93086362469624406752648 : Int)/10^30,(111706402462552047121 : Int)/10^30)
theorem v1364_mg_checked : Scalar.distance (sourceCoefficient 15 30 3 2) v1364_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1364_upper : Scalar.QComplex := ((999997872048802150224957259555 : Int)/10^30,(-2062982759870583517423987707 : Int)/10^30)
theorem v1364_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 30 5) 1) 14) v1364_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1364 : Material (15 : Basis) (30 : Basis) where
  plus := ![v1364_pa,v1364_pb,v1364_pg]
  minus := ![(Primitive.Addresses.material1364 1).one,v1364_mb,v1364_mg]
  upper := v1364_upper
  lower := (Primitive.Addresses.material1364 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1364_pa_checked.trans (by decide +kernel)
    · exact v1364_pb_checked.trans (by decide +kernel)
    · exact v1364_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 30 Primitive.Addresses.material1364
    · exact v1364_mb_checked.trans (by decide +kernel)
    · exact v1364_mg_checked.trans (by decide +kernel)
  upper_error := v1364_upper_checked
  lower_error := reuse_lower_error 15 30 Primitive.Addresses.material1364

def v1365_pa : Scalar.QComplex := ((999999939389120326008733276183 : Int)/10^30,(-348169148079354955635370501 : Int)/10^30)
theorem v1365_pa_checked : Scalar.distance (sourceCoefficient 15 31 1 0) v1365_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1365_pb : Scalar.QComplex := ((-150227159475523423059421 : Int)/10^30,(-431477490750798112608136394 : Int)/10^30)
theorem v1365_pb_checked : Scalar.distance (sourceCoefficient 15 31 1 1) v1365_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1365_pg : Scalar.QComplex := ((-93086423812917637036004 : Int)/10^30,(32409822841085186589 : Int)/10^30)
theorem v1365_pg_checked : Scalar.distance (sourceCoefficient 15 31 1 2) v1365_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1365_mb : Scalar.QComplex := ((-522572745032229374736759 : Int)/10^30,(-431477200452736163316921733 : Int)/10^30)
theorem v1365_mb_checked : Scalar.distance (sourceCoefficient 15 31 3 1) v1365_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1365_mg : Scalar.QComplex := ((-93086361184370364132043 : Int)/10^30,(112739202067077643267 : Int)/10^30)
theorem v1365_mg_checked : Scalar.distance (sourceCoefficient 15 31 3 2) v1365_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1365_upper : Scalar.QComplex := ((999997849098314923902258215443 : Int)/10^30,(-2074077805622088185111592834 : Int)/10^30)
theorem v1365_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 31 5) 1) 14) v1365_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1365 : Material (15 : Basis) (31 : Basis) where
  plus := ![v1365_pa,v1365_pb,v1365_pg]
  minus := ![(Primitive.Addresses.material1365 1).one,v1365_mb,v1365_mg]
  upper := v1365_upper
  lower := (Primitive.Addresses.material1365 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1365_pa_checked.trans (by decide +kernel)
    · exact v1365_pb_checked.trans (by decide +kernel)
    · exact v1365_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 31 Primitive.Addresses.material1365
    · exact v1365_mb_checked.trans (by decide +kernel)
    · exact v1365_mg_checked.trans (by decide +kernel)
  upper_error := v1365_upper_checked
  lower_error := reuse_lower_error 15 31 Primitive.Addresses.material1365

def v1366_pa : Scalar.QComplex := ((999999937714827598796423557273 : Int)/10^30,(-352945237852792755084760624 : Int)/10^30)
theorem v1366_pa_checked : Scalar.distance (sourceCoefficient 15 32 1 0) v1366_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1366_pb : Scalar.QComplex := ((-152287934773019908234502 : Int)/10^30,(-431477489862765194183900621 : Int)/10^30)
theorem v1366_pb_checked : Scalar.distance (sourceCoefficient 15 32 1 1) v1366_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1366_pg : Scalar.QComplex := ((-93086423639199105867736 : Int)/10^30,(32854411978545672811 : Int)/10^30)
theorem v1366_pg_checked : Scalar.distance (sourceCoefficient 15 32 1 2) v1366_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1366_mb : Scalar.QComplex := ((-524633518796072621487941 : Int)/10^30,(-431477197786347307682446179 : Int)/10^30)
theorem v1366_mb_checked : Scalar.distance (sourceCoefficient 15 32 3 1) v1366_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1366_mg : Scalar.QComplex := ((-93086360626991495570166 : Int)/10^30,(113183790889086006478 : Int)/10^30)
theorem v1366_mg_checked : Scalar.distance (sourceCoefficient 15 32 3 2) v1366_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1366_upper : Scalar.QComplex := ((999997839180927024878269067258 : Int)/10^30,(-2078853885392423949422264462 : Int)/10^30)
theorem v1366_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 32 5) 1) 14) v1366_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1366 : Material (15 : Basis) (32 : Basis) where
  plus := ![v1366_pa,v1366_pb,v1366_pg]
  minus := ![(Primitive.Addresses.material1366 1).one,v1366_mb,v1366_mg]
  upper := v1366_upper
  lower := (Primitive.Addresses.material1366 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1366_pa_checked.trans (by decide +kernel)
    · exact v1366_pb_checked.trans (by decide +kernel)
    · exact v1366_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 32 Primitive.Addresses.material1366
    · exact v1366_mb_checked.trans (by decide +kernel)
    · exact v1366_mg_checked.trans (by decide +kernel)
  upper_error := v1366_upper_checked
  lower_error := reuse_lower_error 15 32 Primitive.Addresses.material1366

def v1367_pa : Scalar.QComplex := ((999999935343430643734907215950 : Int)/10^30,(-359601355019774952803208903 : Int)/10^30)
theorem v1367_pa_checked : Scalar.distance (sourceCoefficient 15 33 1 0) v1367_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1367_pb : Scalar.QComplex := ((-155159899594377403982000 : Int)/10^30,(-431477488603284455294203996 : Int)/10^30)
theorem v1367_pb_checked : Scalar.distance (sourceCoefficient 15 33 1 1) v1367_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1367_pg : Scalar.QComplex := ((-93086423392967254781223 : Int)/10^30,(33474006150369902213 : Int)/10^30)
theorem v1367_pg_checked : Scalar.distance (sourceCoefficient 15 33 1 2) v1367_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1367_mb : Scalar.QComplex := ((-527505481461191206212509 : Int)/10^30,(-431477194048490745417383070 : Int)/10^30)
theorem v1367_mb_checked : Scalar.distance (sourceCoefficient 15 33 3 1) v1367_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1367_mg : Scalar.QComplex := ((-93086359846077871368313 : Int)/10^30,(113803384617720011241 : Int)/10^30)
theorem v1367_mg_checked : Scalar.distance (sourceCoefficient 15 33 3 2) v1367_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1367_upper : Scalar.QComplex := ((999997825321679209755143383890 : Int)/10^30,(-2085509988553085496382480500 : Int)/10^30)
theorem v1367_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 33 5) 1) 14) v1367_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1367 : Material (15 : Basis) (33 : Basis) where
  plus := ![v1367_pa,v1367_pb,v1367_pg]
  minus := ![(Primitive.Addresses.material1367 1).one,v1367_mb,v1367_mg]
  upper := v1367_upper
  lower := (Primitive.Addresses.material1367 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1367_pa_checked.trans (by decide +kernel)
    · exact v1367_pb_checked.trans (by decide +kernel)
    · exact v1367_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 33 Primitive.Addresses.material1367
    · exact v1367_mb_checked.trans (by decide +kernel)
    · exact v1367_mg_checked.trans (by decide +kernel)
  upper_error := v1367_upper_checked
  lower_error := reuse_lower_error 15 33 Primitive.Addresses.material1367

def v1368_pa : Scalar.QComplex := ((999999929399082669486826365262 : Int)/10^30,(-375768319149628178655918244 : Int)/10^30)
theorem v1368_pa_checked : Scalar.distance (sourceCoefficient 15 34 1 0) v1368_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1368_pb : Scalar.QComplex := ((-162135580900869515783372 : Int)/10^30,(-431477485438008897150340771 : Int)/10^30)
theorem v1368_pb_checked : Scalar.distance (sourceCoefficient 15 34 1 1) v1368_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1368_pg : Scalar.QComplex := ((-93086422774861861076475 : Int)/10^30,(34978931091306131178 : Int)/10^30)
theorem v1368_pg_checked : Scalar.distance (sourceCoefficient 15 34 1 2) v1368_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1368_mb : Scalar.QComplex := ((-534481157438828115262861 : Int)/10^30,(-431477184863517571370971465 : Int)/10^30)
theorem v1368_mb_checked : Scalar.distance (sourceCoefficient 15 34 3 1) v1368_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1368_mg : Scalar.QComplex := ((-93086357929290263087740 : Int)/10^30,(115308308464906789895 : Int)/10^30)
theorem v1368_mg_checked : Scalar.distance (sourceCoefficient 15 34 3 2) v1368_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1368_upper : Scalar.QComplex := ((999997791474626656317406217607 : Int)/10^30,(-2101676918344739419313866787 : Int)/10^30)
theorem v1368_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 34 5) 1) 14) v1368_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1368 : Material (15 : Basis) (34 : Basis) where
  plus := ![v1368_pa,v1368_pb,v1368_pg]
  minus := ![(Primitive.Addresses.material1368 1).one,v1368_mb,v1368_mg]
  upper := v1368_upper
  lower := (Primitive.Addresses.material1368 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1368_pa_checked.trans (by decide +kernel)
    · exact v1368_pb_checked.trans (by decide +kernel)
    · exact v1368_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 34 Primitive.Addresses.material1368
    · exact v1368_mb_checked.trans (by decide +kernel)
    · exact v1368_mg_checked.trans (by decide +kernel)
  upper_error := v1368_upper_checked
  lower_error := reuse_lower_error 15 34 Primitive.Addresses.material1368

def v1369_pa : Scalar.QComplex := ((999999908779798378703044101765 : Int)/10^30,(-427130419101085245998581165 : Int)/10^30)
theorem v1369_pa_checked : Scalar.distance (sourceCoefficient 15 35 1 0) v1369_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1369_pb : Scalar.QComplex := ((-184297171278066750938079 : Int)/10^30,(-431477474384294840113339055 : Int)/10^30)
theorem v1369_pb_checked : Scalar.distance (sourceCoefficient 15 35 1 1) v1369_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1369_pg : Scalar.QComplex := ((-93086420622816741454810 : Int)/10^30,(39760045480162984638 : Int)/10^30)
theorem v1369_pg_checked : Scalar.distance (sourceCoefficient 15 35 1 2) v1369_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1369_mb : Scalar.QComplex := ((-556642730025395027849227 : Int)/10^30,(-431477154685353255594275529 : Int)/10^30)
theorem v1369_mb_checked : Scalar.distance (sourceCoefficient 15 35 3 1) v1369_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1369_mg : Scalar.QComplex := ((-93086351651359560585885 : Int)/10^30,(120089419216418234942 : Int)/10^30)
theorem v1369_mg_checked : Scalar.distance (sourceCoefficient 15 35 3 2) v1369_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1369_upper : Scalar.QComplex := ((999997682209048092629885017900 : Int)/10^30,(-2153038906211367906011875289 : Int)/10^30)
theorem v1369_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 35 5) 1) 14) v1369_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1369 : Material (15 : Basis) (35 : Basis) where
  plus := ![v1369_pa,v1369_pb,v1369_pg]
  minus := ![(Primitive.Addresses.material1369 1).one,v1369_mb,v1369_mg]
  upper := v1369_upper
  lower := (Primitive.Addresses.material1369 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1369_pa_checked.trans (by decide +kernel)
    · exact v1369_pb_checked.trans (by decide +kernel)
    · exact v1369_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 35 Primitive.Addresses.material1369
    · exact v1369_mb_checked.trans (by decide +kernel)
    · exact v1369_mg_checked.trans (by decide +kernel)
  upper_error := v1369_upper_checked
  lower_error := reuse_lower_error 15 35 Primitive.Addresses.material1369

def v1370_pa : Scalar.QComplex := ((999999901753480805262841174129 : Int)/10^30,(-443275341900602208277135855 : Int)/10^30)
theorem v1370_pa_checked : Scalar.distance (sourceCoefficient 15 36 1 0) v1370_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1370_pb : Scalar.QComplex := ((-191263342091900332224961 : Int)/10^30,(-431477470596211575195008816 : Int)/10^30)
theorem v1370_pb_checked : Scalar.distance (sourceCoefficient 15 36 1 1) v1370_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1370_pg : Scalar.QComplex := ((-93086419887171119667430 : Int)/10^30,(41262918655726924648 : Int)/10^30)
theorem v1370_pg_checked : Scalar.distance (sourceCoefficient 15 36 1 2) v1370_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1370_mb : Scalar.QComplex := ((-563608894976459596724322 : Int)/10^30,(-431477144885779733500792960 : Int)/10^30)
theorem v1370_mb_checked : Scalar.distance (sourceCoefficient 15 36 3 1) v1370_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1370_mg : Scalar.QComplex := ((-93086349618802349096482 : Int)/10^30,(121592291197564767638 : Int)/10^30)
theorem v1370_mg_checked : Scalar.distance (sourceCoefficient 15 36 3 2) v1370_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1370_upper : Scalar.QComplex := ((999997647318068888053169331160 : Int)/10^30,(-2169183792838132165058119091 : Int)/10^30)
theorem v1370_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 36 5) 1) 14) v1370_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1370 : Material (15 : Basis) (36 : Basis) where
  plus := ![v1370_pa,v1370_pb,v1370_pg]
  minus := ![(Primitive.Addresses.material1370 1).one,v1370_mb,v1370_mg]
  upper := v1370_upper
  lower := (Primitive.Addresses.material1370 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1370_pa_checked.trans (by decide +kernel)
    · exact v1370_pb_checked.trans (by decide +kernel)
    · exact v1370_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 36 Primitive.Addresses.material1370
    · exact v1370_mb_checked.trans (by decide +kernel)
    · exact v1370_mg_checked.trans (by decide +kernel)
  upper_error := v1370_upper_checked
  lower_error := reuse_lower_error 15 36 Primitive.Addresses.material1370

def v1371_pa : Scalar.QComplex := ((999999898673751399952961907160 : Int)/10^30,(-450169398041543269035604518 : Int)/10^30)
theorem v1371_pa_checked : Scalar.distance (sourceCoefficient 15 37 1 0) v1371_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1371_pb : Scalar.QComplex := ((-194237972139449234380277 : Int)/10^30,(-431477468932970866302087036 : Int)/10^30)
theorem v1371_pb_checked : Scalar.distance (sourceCoefficient 15 37 1 1) v1371_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1371_pg : Scalar.QComplex := ((-93086419564417859346349 : Int)/10^30,(41904661707198693778 : Int)/10^30)
theorem v1371_pg_checked : Scalar.distance (sourceCoefficient 15 37 1 2) v1371_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1371_mb : Scalar.QComplex := ((-566583522481115962674238 : Int)/10^30,(-431477140655567885237752073 : Int)/10^30)
theorem v1371_mb_checked : Scalar.distance (sourceCoefficient 15 37 3 1) v1371_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1371_mg : Scalar.QComplex := ((-93086348742253858565161 : Int)/10^30,(122234033731564742210 : Int)/10^30)
theorem v1371_mg_checked : Scalar.distance (sourceCoefficient 15 37 3 2) v1371_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1371_upper : Scalar.QComplex := ((999997632339828594261760849352 : Int)/10^30,(-2176077833395852873911155071 : Int)/10^30)
theorem v1371_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 37 5) 1) 14) v1371_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1371 : Material (15 : Basis) (37 : Basis) where
  plus := ![v1371_pa,v1371_pb,v1371_pg]
  minus := ![(Primitive.Addresses.material1371 1).one,v1371_mb,v1371_mg]
  upper := v1371_upper
  lower := (Primitive.Addresses.material1371 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1371_pa_checked.trans (by decide +kernel)
    · exact v1371_pb_checked.trans (by decide +kernel)
    · exact v1371_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 37 Primitive.Addresses.material1371
    · exact v1371_mb_checked.trans (by decide +kernel)
    · exact v1371_mg_checked.trans (by decide +kernel)
  upper_error := v1371_upper_checked
  lower_error := reuse_lower_error 15 37 Primitive.Addresses.material1371

def v1372_pa : Scalar.QComplex := ((999999887912878403831217424316 : Int)/10^30,(-473470411566356211134260875 : Int)/10^30)
theorem v1372_pa_checked : Scalar.distance (sourceCoefficient 15 38 1 0) v1372_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1372_pb : Scalar.QComplex := ((-204291834938332316518789 : Int)/10^30,(-431477463109048711990640243 : Int)/10^30)
theorem v1372_pb_checked : Scalar.distance (sourceCoefficient 15 38 1 1) v1372_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1372_pg : Scalar.QComplex := ((-93086418435349332462172 : Int)/10^30,(44073669787913681330 : Int)/10^30)
theorem v1372_pg_checked : Scalar.distance (sourceCoefficient 15 38 1 2) v1372_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1372_mb : Scalar.QComplex := ((-576637376510703921105717 : Int)/10^30,(-431477126155617113173984971 : Int)/10^30)
theorem v1372_mb_checked : Scalar.distance (sourceCoefficient 15 38 3 1) v1372_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1372_mg : Scalar.QComplex := ((-93086345741429466925351 : Int)/10^30,(124403040030323605402 : Int)/10^30)
theorem v1372_mg_checked : Scalar.distance (sourceCoefficient 15 38 3 2) v1372_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1372_upper : Scalar.QComplex := ((999997581363536132803614893535 : Int)/10^30,(-2199378793644252727588681315 : Int)/10^30)
theorem v1372_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 38 5) 1) 14) v1372_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1372 : Material (15 : Basis) (38 : Basis) where
  plus := ![v1372_pa,v1372_pb,v1372_pg]
  minus := ![(Primitive.Addresses.material1372 1).one,v1372_mb,v1372_mg]
  upper := v1372_upper
  lower := (Primitive.Addresses.material1372 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1372_pa_checked.trans (by decide +kernel)
    · exact v1372_pb_checked.trans (by decide +kernel)
    · exact v1372_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 38 Primitive.Addresses.material1372
    · exact v1372_mb_checked.trans (by decide +kernel)
    · exact v1372_mg_checked.trans (by decide +kernel)
  upper_error := v1372_upper_checked
  lower_error := reuse_lower_error 15 38 Primitive.Addresses.material1372

def v1373_pa : Scalar.QComplex := ((999999881421432493322927086031 : Int)/10^30,(-486987803699925809438055385 : Int)/10^30)
theorem v1373_pa_checked : Scalar.distance (sourceCoefficient 15 39 1 0) v1373_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1373_pb : Scalar.QComplex := ((-210124285306685265464029 : Int)/10^30,(-431477459587311892649293956 : Int)/10^30)
theorem v1373_pb_checked : Scalar.distance (sourceCoefficient 15 39 1 1) v1373_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1373_pg : Scalar.QComplex := ((-93086417753328984702562 : Int)/10^30,(45331955511385811307 : Int)/10^30)
theorem v1373_pg_checked : Scalar.distance (sourceCoefficient 15 39 1 2) v1373_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1373_mb : Scalar.QComplex := ((-582469821668268779809943 : Int)/10^30,(-431477117600739621060922013 : Int)/10^30)
theorem v1373_mb_checked : Scalar.distance (sourceCoefficient 15 39 3 1) v1373_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1373_mg : Scalar.QComplex := ((-93086343973565464841894 : Int)/10^30,(125661324696725610972 : Int)/10^30)
theorem v1373_mg_checked : Scalar.distance (sourceCoefficient 15 39 3 2) v1373_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1373_upper : Scalar.QComplex := ((999997551542307356235462217297 : Int)/10^30,(-2212896154441607865197422949 : Int)/10^30)
theorem v1373_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 39 5) 1) 14) v1373_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1373 : Material (15 : Basis) (39 : Basis) where
  plus := ![v1373_pa,v1373_pb,v1373_pg]
  minus := ![(Primitive.Addresses.material1373 1).one,v1373_mb,v1373_mg]
  upper := v1373_upper
  lower := (Primitive.Addresses.material1373 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1373_pa_checked.trans (by decide +kernel)
    · exact v1373_pb_checked.trans (by decide +kernel)
    · exact v1373_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 39 Primitive.Addresses.material1373
    · exact v1373_mb_checked.trans (by decide +kernel)
    · exact v1373_mg_checked.trans (by decide +kernel)
  upper_error := v1373_upper_checked
  lower_error := reuse_lower_error 15 39 Primitive.Addresses.material1373

def v1374_pa : Scalar.QComplex := ((999999870091070522812724163684 : Int)/10^30,(-509723299524403331707243831 : Int)/10^30)
theorem v1374_pa_checked : Scalar.distance (sourceCoefficient 15 40 1 0) v1374_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1374_pb : Scalar.QComplex := ((-219934139802533549075292 : Int)/10^30,(-431477453426857534539563199 : Int)/10^30)
theorem v1374_pb_checked : Scalar.distance (sourceCoefficient 15 40 1 1) v1374_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1374_pg : Scalar.QComplex := ((-93086416561453088051898 : Int)/10^30,(47448321554567589900 : Int)/10^30)
theorem v1374_pg_checked : Scalar.distance (sourceCoefficient 15 40 1 2) v1374_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1374_mb : Scalar.QComplex := ((-592279667195265247634275 : Int)/10^30,(-431477102974824946298210949 : Int)/10^30)
theorem v1374_mb_checked : Scalar.distance (sourceCoefficient 15 40 3 1) v1374_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1374_mg : Scalar.QComplex := ((-93086340955361434303452 : Int)/10^30,(127777688923352370270 : Int)/10^30)
theorem v1374_mg_checked : Scalar.distance (sourceCoefficient 15 40 3 2) v1374_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1374_upper : Scalar.QComplex := ((999997500972559015989708390215 : Int)/10^30,(-2235631596849058177161231430 : Int)/10^30)
theorem v1374_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 40 5) 1) 14) v1374_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1374 : Material (15 : Basis) (40 : Basis) where
  plus := ![v1374_pa,v1374_pb,v1374_pg]
  minus := ![(Primitive.Addresses.material1374 1).one,v1374_mb,v1374_mg]
  upper := v1374_upper
  lower := (Primitive.Addresses.material1374 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1374_pa_checked.trans (by decide +kernel)
    · exact v1374_pb_checked.trans (by decide +kernel)
    · exact v1374_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 40 Primitive.Addresses.material1374
    · exact v1374_mb_checked.trans (by decide +kernel)
    · exact v1374_mg_checked.trans (by decide +kernel)
  upper_error := v1374_upper_checked
  lower_error := reuse_lower_error 15 40 Primitive.Addresses.material1374

def v1375_pa : Scalar.QComplex := ((999999862603348096094522538528 : Int)/10^30,(-524207291946583856865842075 : Int)/10^30)
theorem v1375_pa_checked : Scalar.distance (sourceCoefficient 15 41 1 0) v1375_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1375_pb : Scalar.QComplex := ((-226183656335180266576323 : Int)/10^30,(-431477449347177398540395938 : Int)/10^30)
theorem v1375_pb_checked : Scalar.distance (sourceCoefficient 15 41 1 1) v1375_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1375_pg : Scalar.QComplex := ((-93086415772877825644382 : Int)/10^30,(48796584633801407749 : Int)/10^30)
theorem v1375_pg_checked : Scalar.distance (sourceCoefficient 15 41 1 2) v1375_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1375_mb : Scalar.QComplex := ((-598529177880351127620847 : Int)/10^30,(-431477093502095029452347132 : Int)/10^30)
theorem v1375_mb_checked : Scalar.distance (sourceCoefficient 15 41 3 1) v1375_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1375_mg : Scalar.QComplex := ((-93086339003296151654687 : Int)/10^30,(129125950820061289707 : Int)/10^30)
theorem v1375_mg_checked : Scalar.distance (sourceCoefficient 15 41 3 2) v1375_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1375_upper : Scalar.QComplex := ((999997468486790798199216325899 : Int)/10^30,(-2250115554775903771106014042 : Int)/10^30)
theorem v1375_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 41 5) 1) 14) v1375_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1375 : Material (15 : Basis) (41 : Basis) where
  plus := ![v1375_pa,v1375_pb,v1375_pg]
  minus := ![(Primitive.Addresses.material1375 1).one,v1375_mb,v1375_mg]
  upper := v1375_upper
  lower := (Primitive.Addresses.material1375 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1375_pa_checked.trans (by decide +kernel)
    · exact v1375_pb_checked.trans (by decide +kernel)
    · exact v1375_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 41 Primitive.Addresses.material1375
    · exact v1375_mb_checked.trans (by decide +kernel)
    · exact v1375_mg_checked.trans (by decide +kernel)
  upper_error := v1375_upper_checked
  lower_error := reuse_lower_error 15 41 Primitive.Addresses.material1375

def v1376_pa : Scalar.QComplex := ((999999856410439769981343037336 : Int)/10^30,(-535890940250043326737947302 : Int)/10^30)
theorem v1376_pa_checked : Scalar.distance (sourceCoefficient 15 42 1 0) v1376_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1376_pb : Scalar.QComplex := ((-231224887418130373711561 : Int)/10^30,(-431477445968320380830351137 : Int)/10^30)
theorem v1376_pb_checked : Scalar.distance (sourceCoefficient 15 42 1 1) v1376_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1376_pg : Scalar.QComplex := ((-93086415120164733107722 : Int)/10^30,(49884173686097490715 : Int)/10^30)
theorem v1376_pg_checked : Scalar.distance (sourceCoefficient 15 42 1 2) v1376_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1376_mb : Scalar.QComplex := ((-603570404170419078718686 : Int)/10^30,(-431477085772883893878784094 : Int)/10^30)
theorem v1376_mb_checked : Scalar.distance (sourceCoefficient 15 42 3 1) v1376_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1376_mg : Scalar.QComplex := ((-93086337412042933213997 : Int)/10^30,(130213538904136261476 : Int)/10^30)
theorem v1376_mg_checked : Scalar.distance (sourceCoefficient 15 42 3 2) v1376_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1376_upper : Scalar.QComplex := ((999997442128974656218826595310 : Int)/10^30,(-2261799174989543596098190544 : Int)/10^30)
theorem v1376_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 15 42 5) 1) 14) v1376_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1376 : Material (15 : Basis) (42 : Basis) where
  plus := ![v1376_pa,v1376_pb,v1376_pg]
  minus := ![(Primitive.Addresses.material1376 1).one,v1376_mb,v1376_mg]
  upper := v1376_upper
  lower := (Primitive.Addresses.material1376 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1376_pa_checked.trans (by decide +kernel)
    · exact v1376_pb_checked.trans (by decide +kernel)
    · exact v1376_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 15 42 Primitive.Addresses.material1376
    · exact v1376_mb_checked.trans (by decide +kernel)
    · exact v1376_mg_checked.trans (by decide +kernel)
  upper_error := v1376_upper_checked
  lower_error := reuse_lower_error 15 42 Primitive.Addresses.material1376

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
