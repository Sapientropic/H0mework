import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B092

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2209_pa : Scalar.QComplex := ((999999766225998576060396156536 : Int)/10^30,(-683774778854554905209262159 : Int)/10^30)
theorem v2209_pa_checked : Scalar.distance (sourceCoefficient 26 39 1 0) v2209_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2209_pb : Scalar.QComplex := ((-295033444896675401220634 : Int)/10^30,(-431477417783323517062612168 : Int)/10^30)
theorem v2209_pb_checked : Scalar.distance (sourceCoefficient 26 39 1 1) v2209_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2209_pg : Scalar.QComplex := ((-93086407882392609422395 : Int)/10^30,(63650152843898824644 : Int)/10^30)
theorem v2209_pg_checked : Scalar.distance (sourceCoefficient 26 39 1 2) v2209_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2209_mb : Scalar.QComplex := ((-667378913567739073530365 : Int)/10^30,(-431477002523986251436358475 : Int)/10^30)
theorem v2209_mb_checked : Scalar.distance (sourceCoefficient 26 39 3 1) v2209_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2209_mg : Scalar.QComplex := ((-93086318294853487985371 : Int)/10^30,(143979506690363053043 : Int)/10^30)
theorem v2209_mg_checked : Scalar.distance (sourceCoefficient 26 39 3 2) v2209_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2209_upper : Scalar.QComplex := ((999997096710578267081053586461 : Int)/10^30,(-2409682637688285197011703684 : Int)/10^30)
theorem v2209_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 39 5) 1) 14) v2209_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2209 : Material (26 : Basis) (39 : Basis) where
  plus := ![v2209_pa,v2209_pb,v2209_pg]
  minus := ![(Primitive.Addresses.material2209 1).one,v2209_mb,v2209_mg]
  upper := v2209_upper
  lower := (Primitive.Addresses.material2209 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2209_pa_checked.trans (by decide +kernel)
    · exact v2209_pb_checked.trans (by decide +kernel)
    · exact v2209_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 39 Primitive.Addresses.material2209
    · exact v2209_mb_checked.trans (by decide +kernel)
    · exact v2209_mg_checked.trans (by decide +kernel)
  upper_error := v2209_upper_checked
  lower_error := reuse_lower_error 26 39 Primitive.Addresses.material2209

def v2210_pa : Scalar.QComplex := ((999999750421586628088406811671 : Int)/10^30,(-706510272009146916646524978 : Int)/10^30)
theorem v2210_pa_checked : Scalar.distance (sourceCoefficient 26 40 1 0) v2210_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2210_pb : Scalar.QComplex := ((-304843298624526641712506 : Int)/10^30,(-431477410335901182815507726 : Int)/10^30)
theorem v2210_pb_checked : Scalar.distance (sourceCoefficient 26 40 1 1) v2210_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2210_pg : Scalar.QComplex := ((-93086406343455598493698 : Int)/10^30,(65766518679972179053 : Int)/10^30)
theorem v2210_pg_checked : Scalar.distance (sourceCoefficient 26 40 1 2) v2210_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2210_mb : Scalar.QComplex := ((-677188757216143383675112 : Int)/10^30,(-431476986611104742480127494 : Int)/10^30)
theorem v2210_mb_checked : Scalar.distance (sourceCoefficient 26 40 3 1) v2210_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2210_mg : Scalar.QComplex := ((-93086314929588651120852 : Int)/10^30,(146095870410383354703 : Int)/10^30)
theorem v2210_mg_checked : Scalar.distance (sourceCoefficient 26 40 3 2) v2210_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2210_upper : Scalar.QComplex := ((999997041666791220925577511747 : Int)/10^30,(-2432418069704049596168758893 : Int)/10^30)
theorem v2210_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 40 5) 1) 14) v2210_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2210 : Material (26 : Basis) (40 : Basis) where
  plus := ![v2210_pa,v2210_pb,v2210_pg]
  minus := ![(Primitive.Addresses.material2210 1).one,v2210_mb,v2210_mg]
  upper := v2210_upper
  lower := (Primitive.Addresses.material2210 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2210_pa_checked.trans (by decide +kernel)
    · exact v2210_pb_checked.trans (by decide +kernel)
    · exact v2210_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 40 Primitive.Addresses.material2210
    · exact v2210_mb_checked.trans (by decide +kernel)
    · exact v2210_mg_checked.trans (by decide +kernel)
  upper_error := v2210_upper_checked
  lower_error := reuse_lower_error 26 40 Primitive.Addresses.material2210

def v2211_pa : Scalar.QComplex := ((999999740083602814873924404237 : Int)/10^30,(-720994262677393727327923240 : Int)/10^30)
theorem v2211_pa_checked : Scalar.distance (sourceCoefficient 26 41 1 0) v2211_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2211_pb : Scalar.QComplex := ((-311092814652651386418035 : Int)/10^30,(-431477405436338581837958177 : Int)/10^30)
theorem v2211_pb_checked : Scalar.distance (sourceCoefficient 26 41 1 1) v2211_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2211_pg : Scalar.QComplex := ((-93086405333779790248856 : Int)/10^30,(67114781623149807969 : Int)/10^30)
theorem v2211_pg_checked : Scalar.distance (sourceCoefficient 26 41 1 2) v2211_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2211_mb : Scalar.QComplex := ((-683438266689185837581885 : Int)/10^30,(-431476976318493101315333276 : Int)/10^30)
theorem v2211_mb_checked : Scalar.distance (sourceCoefficient 26 41 3 1) v2211_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2211_mg : Scalar.QComplex := ((-93086312756423022370963 : Int)/10^30,(147444131980236322809 : Int)/10^30)
theorem v2211_mg_checked : Scalar.distance (sourceCoefficient 26 41 3 2) v2211_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2211_upper : Scalar.QComplex := ((999997006330768888898800193431 : Int)/10^30,(-2446902020957671508515113179 : Int)/10^30)
theorem v2211_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 41 5) 1) 14) v2211_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2211 : Material (26 : Basis) (41 : Basis) where
  plus := ![v2211_pa,v2211_pb,v2211_pg]
  minus := ![(Primitive.Addresses.material2211 1).one,v2211_mb,v2211_mg]
  upper := v2211_upper
  lower := (Primitive.Addresses.material2211 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2211_pa_checked.trans (by decide +kernel)
    · exact v2211_pb_checked.trans (by decide +kernel)
    · exact v2211_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 41 Primitive.Addresses.material2211
    · exact v2211_mb_checked.trans (by decide +kernel)
    · exact v2211_mg_checked.trans (by decide +kernel)
  upper_error := v2211_upper_checked
  lower_error := reuse_lower_error 26 41 Primitive.Addresses.material2211

def v2212_pa : Scalar.QComplex := ((999999731591504417459341186349 : Int)/10^30,(-732677909535943916017070387 : Int)/10^30)
theorem v2212_pa_checked : Scalar.distance (sourceCoefficient 26 42 1 0) v2212_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2212_pb : Scalar.QComplex := ((-316134045319970917300926 : Int)/10^30,(-431477401396115687128899423 : Int)/10^30)
theorem v2212_pb_checked : Scalar.distance (sourceCoefficient 26 42 1 1) v2212_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2212_pg : Scalar.QComplex := ((-93086404502713869475046 : Int)/10^30,(68202370563361352944 : Int)/10^30)
theorem v2212_pg_checked : Scalar.distance (sourceCoefficient 26 42 1 2) v2212_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2212_mb : Scalar.QComplex := ((-688479491992894402148850 : Int)/10^30,(-431476967927916693669966205 : Int)/10^30)
theorem v2212_mb_checked : Scalar.distance (sourceCoefficient 26 42 3 1) v2212_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2212_mg : Scalar.QComplex := ((-93086310986817138825939 : Int)/10^30,(148531719798316340265 : Int)/10^30)
theorem v2212_mg_checked : Scalar.distance (sourceCoefficient 26 42 3 2) v2212_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2212_upper : Scalar.QComplex := ((999996977673768593772874287345 : Int)/10^30,(-2458585635758210722174676076 : Int)/10^30)
theorem v2212_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 42 5) 1) 14) v2212_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2212 : Material (26 : Basis) (42 : Basis) where
  plus := ![v2212_pa,v2212_pb,v2212_pg]
  minus := ![(Primitive.Addresses.material2212 1).one,v2212_mb,v2212_mg]
  upper := v2212_upper
  lower := (Primitive.Addresses.material2212 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2212_pa_checked.trans (by decide +kernel)
    · exact v2212_pb_checked.trans (by decide +kernel)
    · exact v2212_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 42 Primitive.Addresses.material2212
    · exact v2212_mb_checked.trans (by decide +kernel)
    · exact v2212_mg_checked.trans (by decide +kernel)
  upper_error := v2212_upper_checked
  lower_error := reuse_lower_error 26 42 Primitive.Addresses.material2212

def v2213_pa : Scalar.QComplex := ((999999720131489761698203698819 : Int)/10^30,(-748155693789882594645985626 : Int)/10^30)
theorem v2213_pa_checked : Scalar.distance (sourceCoefficient 26 43 1 0) v2213_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2213_pb : Scalar.QComplex := ((-322812360846397897797336 : Int)/10^30,(-431477395922945808799910379 : Int)/10^30)
theorem v2213_pb_checked : Scalar.distance (sourceCoefficient 26 43 1 1) v2213_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2213_pg : Scalar.QComplex := ((-93086403378940474204820 : Int)/10^30,(69643142193298535864 : Int)/10^30)
theorem v2213_pg_checked : Scalar.distance (sourceCoefficient 26 43 1 2) v2213_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2213_mb : Scalar.QComplex := ((-695157800309580195481857 : Int)/10^30,(-431476956691663334111600593 : Int)/10^30)
theorem v2213_mb_checked : Scalar.distance (sourceCoefficient 26 43 3 1) v2213_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2213_mg : Scalar.QComplex := ((-93086308619723135297503 : Int)/10^30,(149972489922022571600 : Int)/10^30)
theorem v2213_mg_checked : Scalar.distance (sourceCoefficient 26 43 3 2) v2213_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2213_upper : Scalar.QComplex := ((999996939500519517678246774677 : Int)/10^30,(-2474063377180862251382937132 : Int)/10^30)
theorem v2213_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 43 5) 1) 14) v2213_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2213 : Material (26 : Basis) (43 : Basis) where
  plus := ![v2213_pa,v2213_pb,v2213_pg]
  minus := ![(Primitive.Addresses.material2213 1).one,v2213_mb,v2213_mg]
  upper := v2213_upper
  lower := (Primitive.Addresses.material2213 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2213_pa_checked.trans (by decide +kernel)
    · exact v2213_pb_checked.trans (by decide +kernel)
    · exact v2213_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 43 Primitive.Addresses.material2213
    · exact v2213_mb_checked.trans (by decide +kernel)
    · exact v2213_mg_checked.trans (by decide +kernel)
  upper_error := v2213_upper_checked
  lower_error := reuse_lower_error 26 43 Primitive.Addresses.material2213

def v2214_pa : Scalar.QComplex := ((999999715733309971443429470205 : Int)/10^30,(-754011471563637472798102396 : Int)/10^30)
theorem v2214_pa_checked : Scalar.distance (sourceCoefficient 26 44 1 0) v2214_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2214_pb : Scalar.QComplex := ((-325338997140928488170313 : Int)/10^30,(-431477393816322730570763733 : Int)/10^30)
theorem v2214_pb_checked : Scalar.distance (sourceCoefficient 26 44 1 1) v2214_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2214_pg : Scalar.QComplex := ((-93086402946994910562685 : Int)/10^30,(70188235620806771323 : Int)/10^30)
theorem v2214_pg_checked : Scalar.distance (sourceCoefficient 26 44 1 2) v2214_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2214_mb : Scalar.QComplex := ((-697684433845407782687578 : Int)/10^30,(-431476952404667713569022994 : Int)/10^30)
theorem v2214_mb_checked : Scalar.distance (sourceCoefficient 26 44 3 1) v2214_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2214_mg : Scalar.QComplex := ((-93086307717386654645468 : Int)/10^30,(150517582773818044680 : Int)/10^30)
theorem v2214_mg_checked : Scalar.distance (sourceCoefficient 26 44 3 2) v2214_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2214_upper : Scalar.QComplex := ((999996924995805072504582262746 : Int)/10^30,(-2479919138642264685278574668 : Int)/10^30)
theorem v2214_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 44 5) 1) 14) v2214_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2214 : Material (26 : Basis) (44 : Basis) where
  plus := ![v2214_pa,v2214_pb,v2214_pg]
  minus := ![(Primitive.Addresses.material2214 1).one,v2214_mb,v2214_mg]
  upper := v2214_upper
  lower := (Primitive.Addresses.material2214 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2214_pa_checked.trans (by decide +kernel)
    · exact v2214_pb_checked.trans (by decide +kernel)
    · exact v2214_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 44 Primitive.Addresses.material2214
    · exact v2214_mb_checked.trans (by decide +kernel)
    · exact v2214_mg_checked.trans (by decide +kernel)
  upper_error := v2214_upper_checked
  lower_error := reuse_lower_error 26 44 Primitive.Addresses.material2214

def v2215_pa : Scalar.QComplex := ((999999713532386950471715217065 : Int)/10^30,(-756924794174007252325073151 : Int)/10^30)
theorem v2215_pa_checked : Scalar.distance (sourceCoefficient 26 45 1 0) v2215_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2215_pb : Scalar.QComplex := ((-326596030265468801102244 : Int)/10^30,(-431477392760902721792976311 : Int)/10^30)
theorem v2215_pb_checked : Scalar.distance (sourceCoefficient 26 45 1 1) v2215_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2215_pg : Scalar.QComplex := ((-93086402730709369845184 : Int)/10^30,(70459426411684637406 : Int)/10^30)
theorem v2215_pg_checked : Scalar.distance (sourceCoefficient 26 45 1 2) v2215_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2215_mb : Scalar.QComplex := ((-698941465591117280878715 : Int)/10^30,(-431476950264485125964343803 : Int)/10^30)
theorem v2215_mb_checked : Scalar.distance (sourceCoefficient 26 45 3 1) v2215_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2215_mg : Scalar.QComplex := ((-93086307267075755913176 : Int)/10^30,(150788773277074504788 : Int)/10^30)
theorem v2215_mg_checked : Scalar.distance (sourceCoefficient 26 45 3 2) v2215_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2215_upper : Scalar.QComplex := ((999996917766754798613586626460 : Int)/10^30,(-2482832453114989191552998543 : Int)/10^30)
theorem v2215_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 45 5) 1) 14) v2215_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2215 : Material (26 : Basis) (45 : Basis) where
  plus := ![v2215_pa,v2215_pb,v2215_pg]
  minus := ![(Primitive.Addresses.material2215 1).one,v2215_mb,v2215_mg]
  upper := v2215_upper
  lower := (Primitive.Addresses.material2215 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2215_pa_checked.trans (by decide +kernel)
    · exact v2215_pb_checked.trans (by decide +kernel)
    · exact v2215_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 45 Primitive.Addresses.material2215
    · exact v2215_mb_checked.trans (by decide +kernel)
    · exact v2215_mg_checked.trans (by decide +kernel)
  upper_error := v2215_upper_checked
  lower_error := reuse_lower_error 26 45 Primitive.Addresses.material2215

def v2216_pa : Scalar.QComplex := ((999999701011991317250846248132 : Int)/10^30,(-773289032620836393191345784 : Int)/10^30)
theorem v2216_pa_checked : Scalar.distance (sourceCoefficient 26 46 1 0) v2216_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2216_pb : Scalar.QComplex := ((-333656830750745277805226 : Int)/10^30,(-431477386741826959876509204 : Int)/10^30)
theorem v2216_pb_checked : Scalar.distance (sourceCoefficient 26 46 1 1) v2216_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2216_pg : Scalar.QComplex := ((-93086401498695902778944 : Int)/10^30,(71982714887049913341 : Int)/10^30)
theorem v2216_pg_checked : Scalar.distance (sourceCoefficient 26 46 1 2) v2216_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2216_mb : Scalar.QComplex := ((-706002258253143748964760 : Int)/10^30,(-431476938152258793080163964 : Int)/10^30)
theorem v2216_mb_checked : Scalar.distance (sourceCoefficient 26 46 3 1) v2216_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2216_mg : Scalar.QComplex := ((-93086304720533399707765 : Int)/10^30,(152312060122077729370 : Int)/10^30)
theorem v2216_mg_checked : Scalar.distance (sourceCoefficient 26 46 3 2) v2216_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2216_upper : Scalar.QComplex := ((999996877003186805939378842292 : Int)/10^30,(-2499196645580140422827848499 : Int)/10^30)
theorem v2216_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 46 5) 1) 14) v2216_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2216 : Material (26 : Basis) (46 : Basis) where
  plus := ![v2216_pa,v2216_pb,v2216_pg]
  minus := ![(Primitive.Addresses.material2216 1).one,v2216_mb,v2216_mg]
  upper := v2216_upper
  lower := (Primitive.Addresses.material2216 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2216_pa_checked.trans (by decide +kernel)
    · exact v2216_pb_checked.trans (by decide +kernel)
    · exact v2216_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 46 Primitive.Addresses.material2216
    · exact v2216_mb_checked.trans (by decide +kernel)
    · exact v2216_mg_checked.trans (by decide +kernel)
  upper_error := v2216_upper_checked
  lower_error := reuse_lower_error 26 46 Primitive.Addresses.material2216

def v2217_pa : Scalar.QComplex := ((999999697958991996788106738819 : Int)/10^30,(-777227074140918788237034866 : Int)/10^30)
theorem v2217_pa_checked : Scalar.distance (sourceCoefficient 26 47 1 0) v2217_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2217_pb : Scalar.QComplex := ((-335356007002908932048108 : Int)/10^30,(-431477385270342842783325908 : Int)/10^30)
theorem v2217_pb_checked : Scalar.distance (sourceCoefficient 26 47 1 1) v2217_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2217_pg : Scalar.QComplex := ((-93086401197871412136277 : Int)/10^30,(72349293097782731115 : Int)/10^30)
theorem v2217_pg_checked : Scalar.distance (sourceCoefficient 26 47 1 2) v2217_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2217_mb : Scalar.QComplex := ((-707701432602801908469136 : Int)/10^30,(-431476935214462646328076415 : Int)/10^30)
theorem v2217_mb_checked : Scalar.distance (sourceCoefficient 26 47 3 1) v2217_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2217_mg : Scalar.QComplex := ((-93086304103368535283112 : Int)/10^30,(152678637936718739044 : Int)/10^30)
theorem v2217_mg_checked : Scalar.distance (sourceCoefficient 26 47 3 2) v2217_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2217_upper : Scalar.QComplex := ((999996867153489625234251350019 : Int)/10^30,(-2503134675965772707379399906 : Int)/10^30)
theorem v2217_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 47 5) 1) 14) v2217_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2217 : Material (26 : Basis) (47 : Basis) where
  plus := ![v2217_pa,v2217_pb,v2217_pg]
  minus := ![(Primitive.Addresses.material2217 1).one,v2217_mb,v2217_mg]
  upper := v2217_upper
  lower := (Primitive.Addresses.material2217 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2217_pa_checked.trans (by decide +kernel)
    · exact v2217_pb_checked.trans (by decide +kernel)
    · exact v2217_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 47 Primitive.Addresses.material2217
    · exact v2217_mb_checked.trans (by decide +kernel)
    · exact v2217_mg_checked.trans (by decide +kernel)
  upper_error := v2217_upper_checked
  lower_error := reuse_lower_error 26 47 Primitive.Addresses.material2217

def v2218_pa : Scalar.QComplex := ((999999676262994116333725111465 : Int)/10^30,(-804657633383095155520221526 : Int)/10^30)
theorem v2218_pa_checked : Scalar.distance (sourceCoefficient 26 48 1 0) v2218_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2218_pb : Scalar.QComplex := ((-347191675642114323546844 : Int)/10^30,(-431477374773158824236923954 : Int)/10^30)
theorem v2218_pb_checked : Scalar.distance (sourceCoefficient 26 48 1 1) v2218_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2218_pg : Scalar.QComplex := ((-93086399055745132911023 : Int)/10^30,(74902705813127974750 : Int)/10^30)
theorem v2218_pg_checked : Scalar.distance (sourceCoefficient 26 48 1 2) v2218_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2218_mb : Scalar.QComplex := ((-719537087776449916425457 : Int)/10^30,(-431476914503633559456216414 : Int)/10^30)
theorem v2218_mb_checked : Scalar.distance (sourceCoefficient 26 48 3 1) v2218_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2218_mg : Scalar.QComplex := ((-93086299757762881766071 : Int)/10^30,(155232047852753230844 : Int)/10^30)
theorem v2218_mg_checked : Scalar.distance (sourceCoefficient 26 48 3 2) v2218_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2218_upper : Scalar.QComplex := ((999996798114867287319216051342 : Int)/10^30,(-2530565156908029207166433343 : Int)/10^30)
theorem v2218_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 48 5) 1) 14) v2218_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2218 : Material (26 : Basis) (48 : Basis) where
  plus := ![v2218_pa,v2218_pb,v2218_pg]
  minus := ![(Primitive.Addresses.material2218 1).one,v2218_mb,v2218_mg]
  upper := v2218_upper
  lower := (Primitive.Addresses.material2218 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2218_pa_checked.trans (by decide +kernel)
    · exact v2218_pb_checked.trans (by decide +kernel)
    · exact v2218_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 48 Primitive.Addresses.material2218
    · exact v2218_mb_checked.trans (by decide +kernel)
    · exact v2218_mg_checked.trans (by decide +kernel)
  upper_error := v2218_upper_checked
  lower_error := reuse_lower_error 26 48 Primitive.Addresses.material2218

def v2219_pa : Scalar.QComplex := ((999999658286795044493768728783 : Int)/10^30,(-826696010116837337563159367 : Int)/10^30)
theorem v2219_pa_checked : Scalar.distance (sourceCoefficient 26 49 1 0) v2219_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2219_pb : Scalar.QComplex := ((-356700738838656763735037 : Int)/10^30,(-431477366025864112390465761 : Int)/10^30)
theorem v2219_pb_checked : Scalar.distance (sourceCoefficient 26 49 1 1) v2219_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2219_pg : Scalar.QComplex := ((-93086397275509732850936 : Int)/10^30,(76954179520074052211 : Int)/10^30)
theorem v2219_pg_checked : Scalar.distance (sourceCoefficient 26 49 1 2) v2219_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2219_mb : Scalar.QComplex := ((-729046139883812170089565 : Int)/10^30,(-431476897550448838319381567 : Int)/10^30)
theorem v2219_mb_checked : Scalar.distance (sourceCoefficient 26 49 3 1) v2219_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2219_mg : Scalar.QComplex := ((-93086296207198730420419 : Int)/10^30,(157283519259578918804 : Int)/10^30)
theorem v2219_mg_checked : Scalar.distance (sourceCoefficient 26 49 3 2) v2219_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2219_upper : Scalar.QComplex := ((999996742102456052396702613590 : Int)/10^30,(-2552603469792909243930506683 : Int)/10^30)
theorem v2219_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 49 5) 1) 14) v2219_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2219 : Material (26 : Basis) (49 : Basis) where
  plus := ![v2219_pa,v2219_pb,v2219_pg]
  minus := ![(Primitive.Addresses.material2219 1).one,v2219_mb,v2219_mg]
  upper := v2219_upper
  lower := (Primitive.Addresses.material2219 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2219_pa_checked.trans (by decide +kernel)
    · exact v2219_pb_checked.trans (by decide +kernel)
    · exact v2219_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 49 Primitive.Addresses.material2219
    · exact v2219_mb_checked.trans (by decide +kernel)
    · exact v2219_mg_checked.trans (by decide +kernel)
  upper_error := v2219_upper_checked
  lower_error := reuse_lower_error 26 49 Primitive.Addresses.material2219

def v2220_pa : Scalar.QComplex := ((999999656154504398767431704297 : Int)/10^30,(-829271290334315318707340438 : Int)/10^30)
theorem v2220_pa_checked : Scalar.distance (sourceCoefficient 26 50 1 0) v2220_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2220_pb : Scalar.QComplex := ((-357811914243567055716621 : Int)/10^30,(-431477364985471253709336160 : Int)/10^30)
theorem v2220_pb_checked : Scalar.distance (sourceCoefficient 26 50 1 1) v2220_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2220_pg : Scalar.QComplex := ((-93086397064039532963388 : Int)/10^30,(77193903148644370152 : Int)/10^30)
theorem v2220_pg_checked : Scalar.distance (sourceCoefficient 26 50 1 2) v2220_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2220_mb : Scalar.QComplex := ((-730157313977168896111406 : Int)/10^30,(-431476895551162038068941101 : Int)/10^30)
theorem v2220_mb_checked : Scalar.distance (sourceCoefficient 26 50 3 1) v2220_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2220_mg : Scalar.QComplex := ((-93086295788857914568143 : Int)/10^30,(157523242616399915679 : Int)/10^30)
theorem v2220_mg_checked : Scalar.distance (sourceCoefficient 26 50 3 2) v2220_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2220_upper : Scalar.QComplex := ((999996735525468554696141462268 : Int)/10^30,(-2555178742494669640178658768 : Int)/10^30)
theorem v2220_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 50 5) 1) 14) v2220_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2220 : Material (26 : Basis) (50 : Basis) where
  plus := ![v2220_pa,v2220_pb,v2220_pg]
  minus := ![(Primitive.Addresses.material2220 1).one,v2220_mb,v2220_mg]
  upper := v2220_upper
  lower := (Primitive.Addresses.material2220 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2220_pa_checked.trans (by decide +kernel)
    · exact v2220_pb_checked.trans (by decide +kernel)
    · exact v2220_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 50 Primitive.Addresses.material2220
    · exact v2220_mb_checked.trans (by decide +kernel)
    · exact v2220_mg_checked.trans (by decide +kernel)
  upper_error := v2220_upper_checked
  lower_error := reuse_lower_error 26 50 Primitive.Addresses.material2220

def v2221_pa : Scalar.QComplex := ((999999646720523838601714044397 : Int)/10^30,(-840570536907170149856565712 : Int)/10^30)
theorem v2221_pa_checked : Scalar.distance (sourceCoefficient 26 51 1 0) v2221_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2221_pb : Scalar.QComplex := ((-362687284604154697784267 : Int)/10^30,(-431477360375569244027012771 : Int)/10^30)
theorem v2221_pb_checked : Scalar.distance (sourceCoefficient 26 51 1 1) v2221_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2221_pg : Scalar.QComplex := ((-93086396127684452316807 : Int)/10^30,(78245709614404548901 : Int)/10^30)
theorem v2221_pg_checked : Scalar.distance (sourceCoefficient 26 51 1 2) v2221_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2221_mb : Scalar.QComplex := ((-735032678544295525422858 : Int)/10^30,(-431476886734036702206586431 : Int)/10^30)
theorem v2221_mb_checked : Scalar.distance (sourceCoefficient 26 51 3 1) v2221_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2221_mg : Scalar.QComplex := ((-93086293944841574223019 : Int)/10^30,(158575047882492214564 : Int)/10^30)
theorem v2221_mg_checked : Scalar.distance (sourceCoefficient 26 51 3 2) v2221_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2221_upper : Scalar.QComplex := ((999996706590027520230599300744 : Int)/10^30,(-2566477955956429400985895622 : Int)/10^30)
theorem v2221_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 51 5) 1) 14) v2221_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2221 : Material (26 : Basis) (51 : Basis) where
  plus := ![v2221_pa,v2221_pb,v2221_pg]
  minus := ![(Primitive.Addresses.material2221 1).one,v2221_mb,v2221_mg]
  upper := v2221_upper
  lower := (Primitive.Addresses.material2221 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2221_pa_checked.trans (by decide +kernel)
    · exact v2221_pb_checked.trans (by decide +kernel)
    · exact v2221_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 51 Primitive.Addresses.material2221
    · exact v2221_mb_checked.trans (by decide +kernel)
    · exact v2221_mg_checked.trans (by decide +kernel)
  upper_error := v2221_upper_checked
  lower_error := reuse_lower_error 26 51 Primitive.Addresses.material2221

def v2222_pa : Scalar.QComplex := ((999999626095468072871819308522 : Int)/10^30,(-864759460225592077181350925 : Int)/10^30)
theorem v2222_pa_checked : Scalar.distance (sourceCoefficient 26 52 1 0) v2222_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2222_pb : Scalar.QComplex := ((-373124260023232364273247 : Int)/10^30,(-431477350259970209436774622 : Int)/10^30)
theorem v2222_pb_checked : Scalar.distance (sourceCoefficient 26 52 1 1) v2222_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2222_pg : Scalar.QComplex := ((-93086394076564599667332 : Int)/10^30,(80497369994328203955 : Int)/10^30)
theorem v2222_pg_checked : Scalar.distance (sourceCoefficient 26 52 1 2) v2222_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2222_mb : Scalar.QComplex := ((-745469641347903872865481 : Int)/10^30,(-431476867611801711375430595 : Int)/10^30)
theorem v2222_mb_checked : Scalar.distance (sourceCoefficient 26 52 3 1) v2222_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2222_mg : Scalar.QComplex := ((-93086289950640988444050 : Int)/10^30,(160826705653995750381 : Int)/10^30)
theorem v2222_mg_checked : Scalar.distance (sourceCoefficient 26 52 3 2) v2222_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2222_upper : Scalar.QComplex := ((999996644217115227483951481548 : Int)/10^30,(-2590666807651316314846922652 : Int)/10^30)
theorem v2222_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 52 5) 1) 14) v2222_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2222 : Material (26 : Basis) (52 : Basis) where
  plus := ![v2222_pa,v2222_pb,v2222_pg]
  minus := ![(Primitive.Addresses.material2222 1).one,v2222_mb,v2222_mg]
  upper := v2222_upper
  lower := (Primitive.Addresses.material2222 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2222_pa_checked.trans (by decide +kernel)
    · exact v2222_pb_checked.trans (by decide +kernel)
    · exact v2222_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 52 Primitive.Addresses.material2222
    · exact v2222_mb_checked.trans (by decide +kernel)
    · exact v2222_mg_checked.trans (by decide +kernel)
  upper_error := v2222_upper_checked
  lower_error := reuse_lower_error 26 52 Primitive.Addresses.material2222

def v2223_pa : Scalar.QComplex := ((999999622886677019197535910849 : Int)/10^30,(-868462148712968698117019798 : Int)/10^30)
theorem v2223_pa_checked : Scalar.distance (sourceCoefficient 26 53 1 0) v2223_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2223_pb : Scalar.QComplex := ((-374721886669813534199598 : Int)/10^30,(-431477348681830880387294051 : Int)/10^30)
theorem v2223_pb_checked : Scalar.distance (sourceCoefficient 26 53 1 1) v2223_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2223_pg : Scalar.QComplex := ((-93086393756984228737610 : Int)/10^30,(80842040024742348539 : Int)/10^30)
theorem v2223_pg_checked : Scalar.distance (sourceCoefficient 26 53 1 2) v2223_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2223_mb : Scalar.QComplex := ((-747067266037752462912078 : Int)/10^30,(-431476864654983128372885019 : Int)/10^30)
theorem v2223_mb_checked : Scalar.distance (sourceCoefficient 26 53 3 1) v2223_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2223_mg : Scalar.QComplex := ((-93086289333626023623214 : Int)/10^30,(161171375280290023697 : Int)/10^30)
theorem v2223_mg_checked : Scalar.distance (sourceCoefficient 26 53 3 2) v2223_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2223_upper : Scalar.QComplex := ((999996634617824528990590513528 : Int)/10^30,(-2594369485085891122786930210 : Int)/10^30)
theorem v2223_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 53 5) 1) 14) v2223_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2223 : Material (26 : Basis) (53 : Basis) where
  plus := ![v2223_pa,v2223_pb,v2223_pg]
  minus := ![(Primitive.Addresses.material2223 1).one,v2223_mb,v2223_mg]
  upper := v2223_upper
  lower := (Primitive.Addresses.material2223 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2223_pa_checked.trans (by decide +kernel)
    · exact v2223_pb_checked.trans (by decide +kernel)
    · exact v2223_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 53 Primitive.Addresses.material2223
    · exact v2223_mb_checked.trans (by decide +kernel)
    · exact v2223_mg_checked.trans (by decide +kernel)
  upper_error := v2223_upper_checked
  lower_error := reuse_lower_error 26 53 Primitive.Addresses.material2223

def v2224_pa : Scalar.QComplex := ((999999621250051230660965340282 : Int)/10^30,(-870344618003210482622000807 : Int)/10^30)
theorem v2224_pa_checked : Scalar.distance (sourceCoefficient 26 54 1 0) v2224_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2224_pb : Scalar.QComplex := ((-375534129748117857606018 : Int)/10^30,(-431477347876470931243141985 : Int)/10^30)
theorem v2224_pb_checked : Scalar.distance (sourceCoefficient 26 54 1 1) v2224_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2224_pg : Scalar.QComplex := ((-93086393593936720287378 : Int)/10^30,(81017272359099109624 : Int)/10^30)
theorem v2224_pg_checked : Scalar.distance (sourceCoefficient 26 54 1 2) v2224_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2224_mb : Scalar.QComplex := ((-747879508118632202877512 : Int)/10^30,(-431476863148694284594674232 : Int)/10^30)
theorem v2224_mb_checked : Scalar.distance (sourceCoefficient 26 54 3 1) v2224_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2224_mg : Scalar.QComplex := ((-93086289019360963504505 : Int)/10^30,(161346607408697121782 : Int)/10^30)
theorem v2224_mg_checked : Scalar.distance (sourceCoefficient 26 54 3 2) v2224_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2224_upper : Scalar.QComplex := ((999996629732229959338539987497 : Int)/10^30,(-2596251948747748392370770368 : Int)/10^30)
theorem v2224_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 26 54 5) 1) 14) v2224_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2224 : Material (26 : Basis) (54 : Basis) where
  plus := ![v2224_pa,v2224_pb,v2224_pg]
  minus := ![(Primitive.Addresses.material2224 1).one,v2224_mb,v2224_mg]
  upper := v2224_upper
  lower := (Primitive.Addresses.material2224 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2224_pa_checked.trans (by decide +kernel)
    · exact v2224_pb_checked.trans (by decide +kernel)
    · exact v2224_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 26 54 Primitive.Addresses.material2224
    · exact v2224_mb_checked.trans (by decide +kernel)
    · exact v2224_mg_checked.trans (by decide +kernel)
  upper_error := v2224_upper_checked
  lower_error := reuse_lower_error 26 54 Primitive.Addresses.material2224

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
