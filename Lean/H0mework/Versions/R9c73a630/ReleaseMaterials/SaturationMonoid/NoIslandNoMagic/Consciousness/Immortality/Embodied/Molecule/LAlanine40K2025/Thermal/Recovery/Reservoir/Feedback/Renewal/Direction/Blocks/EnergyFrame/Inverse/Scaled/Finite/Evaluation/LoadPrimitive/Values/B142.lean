import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B094
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B095

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2273_pa : Scalar.QComplex := ((999999842396157481638497357034 : Int)/10^30,(-561433575944431585554433302 : Int)/10^30)
theorem v2273_pa_checked : Scalar.distance (sourceCoefficient 27 33 1 0) v2273_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2273_pb : Scalar.QComplex := ((-242245967460824624276627 : Int)/10^30,(-431477452830334172595854587 : Int)/10^30)
theorem v2273_pb_checked : Scalar.distance (sourceCoefficient 27 33 1 1) v2273_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2273_pg : Scalar.QComplex := ((-93086415208096180962014 : Int)/10^30,(52261847198797494168 : Int)/10^30)
theorem v2273_pg_checked : Scalar.distance (sourceCoefficient 27 33 1 2) v2273_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2273_mb : Scalar.QComplex := ((-614591486031070389813086 : Int)/10^30,(-431477083124199424776769705 : Int)/10^30)
theorem v2273_mb_checked : Scalar.distance (sourceCoefficient 27 33 3 1) v2273_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2273_mg : Scalar.QComplex := ((-93086335448149193307065 : Int)/10^30,(132591211607400630315 : Int)/10^30)
theorem v2273_mg_checked : Scalar.distance (sourceCoefficient 27 33 3 2) v2273_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2273_upper : Scalar.QComplex := ((999997384030441241798226675538 : Int)/10^30,(-2287341748453796572960140005 : Int)/10^30)
theorem v2273_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 33 5) 1) 14) v2273_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2273 : Material (27 : Basis) (33 : Basis) where
  plus := ![v2273_pa,v2273_pb,v2273_pg]
  minus := ![(Primitive.Addresses.material2273 1).one,v2273_mb,v2273_mg]
  upper := v2273_upper
  lower := (Primitive.Addresses.material2273 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2273_pa_checked.trans (by decide +kernel)
    · exact v2273_pb_checked.trans (by decide +kernel)
    · exact v2273_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 33 Primitive.Addresses.material2273
    · exact v2273_mb_checked.trans (by decide +kernel)
    · exact v2273_mg_checked.trans (by decide +kernel)
  upper_error := v2273_upper_checked
  lower_error := reuse_lower_error 27 33 Primitive.Addresses.material2273

def v2274_pa : Scalar.QComplex := ((999999833188795023139375198345 : Int)/10^30,(-577600538545232957758966143 : Int)/10^30)
theorem v2274_pa_checked : Scalar.distance (sourceCoefficient 27 34 1 0) v2274_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2274_pb : Scalar.QComplex := ((-249221648327482404417493 : Int)/10^30,(-431477448726447022484142276 : Int)/10^30)
theorem v2274_pb_checked : Scalar.distance (sourceCoefficient 27 34 1 1) v2274_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2274_pg : Scalar.QComplex := ((-93086414336872146974492 : Int)/10^30,(53766772021122074905 : Int)/10^30)
theorem v2274_pg_checked : Scalar.distance (sourceCoefficient 27 34 1 2) v2274_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2274_mb : Scalar.QComplex := ((-621567160758893600601938 : Int)/10^30,(-431477073000615387807720193 : Int)/10^30)
theorem v2274_mb_checked : Scalar.distance (sourceCoefficient 27 34 3 1) v2274_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2274_mg : Scalar.QComplex := ((-93086333278243141347867 : Int)/10^30,(134096135117545818382 : Int)/10^30)
theorem v2274_mg_checked : Scalar.distance (sourceCoefficient 27 34 3 2) v2274_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2274_upper : Scalar.QComplex := ((999997346920381702991006782629 : Int)/10^30,(-2303508671084733938130816167 : Int)/10^30)
theorem v2274_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 34 5) 1) 14) v2274_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2274 : Material (27 : Basis) (34 : Basis) where
  plus := ![v2274_pa,v2274_pb,v2274_pg]
  minus := ![(Primitive.Addresses.material2274 1).one,v2274_mb,v2274_mg]
  upper := v2274_upper
  lower := (Primitive.Addresses.material2274 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2274_pa_checked.trans (by decide +kernel)
    · exact v2274_pb_checked.trans (by decide +kernel)
    · exact v2274_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 34 Primitive.Addresses.material2274
    · exact v2274_mb_checked.trans (by decide +kernel)
    · exact v2274_mg_checked.trans (by decide +kernel)
  upper_error := v2274_upper_checked
  lower_error := reuse_lower_error 27 34 Primitive.Addresses.material2274

def v2275_pa : Scalar.QComplex := ((999999802202983401314018447477 : Int)/10^30,(-628962633288903886823371670 : Int)/10^30)
theorem v2275_pa_checked : Scalar.distance (sourceCoefficient 27 35 1 0) v2275_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2275_pb : Scalar.QComplex := ((-271383237206651219286663 : Int)/10^30,(-431477434690783986461070786 : Int)/10^30)
theorem v2275_pb_checked : Scalar.distance (sourceCoefficient 27 35 1 1) v2275_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2275_pg : Scalar.QComplex := ((-93086411380674513390985 : Int)/10^30,(58547886006000413464 : Int)/10^30)
theorem v2275_pg_checked : Scalar.distance (sourceCoefficient 27 35 1 2) v2275_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2275_mb : Scalar.QComplex := ((-643728729274144983818721 : Int)/10^30,(-431477039840504496091899171 : Int)/10^30)
theorem v2275_mb_checked : Scalar.distance (sourceCoefficient 27 35 3 1) v2275_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2275_mg : Scalar.QComplex := ((-93086326196160572922165 : Int)/10^30,(138877244771131497083 : Int)/10^30)
theorem v2275_mg_checked : Scalar.distance (sourceCoefficient 27 35 3 2) v2275_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2275_upper : Scalar.QComplex := ((999997227288300236153060840613 : Int)/10^30,(-2354870635851898313571639759 : Int)/10^30)
theorem v2275_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 35 5) 1) 14) v2275_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2275 : Material (27 : Basis) (35 : Basis) where
  plus := ![v2275_pa,v2275_pb,v2275_pg]
  minus := ![(Primitive.Addresses.material2275 1).one,v2275_mb,v2275_mg]
  upper := v2275_upper
  lower := (Primitive.Addresses.material2275 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2275_pa_checked.trans (by decide +kernel)
    · exact v2275_pb_checked.trans (by decide +kernel)
    · exact v2275_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 35 Primitive.Addresses.material2275
    · exact v2275_mb_checked.trans (by decide +kernel)
    · exact v2275_mg_checked.trans (by decide +kernel)
  upper_error := v2275_upper_checked
  lower_error := reuse_lower_error 27 35 Primitive.Addresses.material2275

def v2276_pa : Scalar.QComplex := ((999999791918100016763444699744 : Int)/10^30,(-645107554341441586847600187 : Int)/10^30)
theorem v2276_pa_checked : Scalar.distance (sourceCoefficient 27 36 1 0) v2276_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2276_pb : Scalar.QComplex := ((-278349407517963285383584 : Int)/10^30,(-431477429965368800287361903 : Int)/10^30)
theorem v2276_pb_checked : Scalar.distance (sourceCoefficient 27 36 1 1) v2276_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2276_pg : Scalar.QComplex := ((-93086410392255344295038 : Int)/10^30,(60050759046047635117 : Int)/10^30)
theorem v2276_pg_checked : Scalar.distance (sourceCoefficient 27 36 1 2) v2276_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2276_mb : Scalar.QComplex := ((-650694892913812992434797 : Int)/10^30,(-431477029103599835407985306 : Int)/10^30)
theorem v2276_mb_checked : Scalar.distance (sourceCoefficient 27 36 3 1) v2276_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2276_mg : Scalar.QComplex := ((-93086323910830025188164 : Int)/10^30,(140380116398629175053 : Int)/10^30)
theorem v2276_mg_checked : Scalar.distance (sourceCoefficient 27 36 3 2) v2276_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2276_upper : Scalar.QComplex := ((999997189138763088844693884121 : Int)/10^30,(-2371015515107696937088621869 : Int)/10^30)
theorem v2276_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 36 5) 1) 14) v2276_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2276 : Material (27 : Basis) (36 : Basis) where
  plus := ![v2276_pa,v2276_pb,v2276_pg]
  minus := ![(Primitive.Addresses.material2276 1).one,v2276_mb,v2276_mg]
  upper := v2276_upper
  lower := (Primitive.Addresses.material2276 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2276_pa_checked.trans (by decide +kernel)
    · exact v2276_pb_checked.trans (by decide +kernel)
    · exact v2276_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 36 Primitive.Addresses.material2276
    · exact v2276_mb_checked.trans (by decide +kernel)
    · exact v2276_mg_checked.trans (by decide +kernel)
  upper_error := v2276_upper_checked
  lower_error := reuse_lower_error 27 36 Primitive.Addresses.material2276

def v2277_pa : Scalar.QComplex := ((999999787446927871615698475132 : Int)/10^30,(-652001609720374947967848378 : Int)/10^30)
theorem v2277_pa_checked : Scalar.distance (sourceCoefficient 27 37 1 0) v2277_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2277_pb : Scalar.QComplex := ((-281324037346319394651661 : Int)/10^30,(-431477427901877253583648882 : Int)/10^30)
theorem v2277_pb_checked : Scalar.distance (sourceCoefficient 27 37 1 1) v2277_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2277_pg : Scalar.QComplex := ((-93086409961565053543386 : Int)/10^30,(60692502038408924223 : Int)/10^30)
theorem v2277_pg_checked : Scalar.distance (sourceCoefficient 27 37 1 2) v2277_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2277_mb : Scalar.QComplex := ((-653669519853878200710811 : Int)/10^30,(-431477024473137487519340648 : Int)/10^30)
theorem v2277_mb_checked : Scalar.distance (sourceCoefficient 27 37 3 1) v2277_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2277_mg : Scalar.QComplex := ((-93086322926344595425843 : Int)/10^30,(141021858780373895651 : Int)/10^30)
theorem v2277_mg_checked : Scalar.distance (sourceCoefficient 27 37 3 2) v2277_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2277_upper : Scalar.QComplex := ((999997172769083442762089864253 : Int)/10^30,(-2377909552501907142963533888 : Int)/10^30)
theorem v2277_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 37 5) 1) 14) v2277_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2277 : Material (27 : Basis) (37 : Basis) where
  plus := ![v2277_pa,v2277_pb,v2277_pg]
  minus := ![(Primitive.Addresses.material2277 1).one,v2277_mb,v2277_mg]
  upper := v2277_upper
  lower := (Primitive.Addresses.material2277 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2277_pa_checked.trans (by decide +kernel)
    · exact v2277_pb_checked.trans (by decide +kernel)
    · exact v2277_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 37 Primitive.Addresses.material2277
    · exact v2277_mb_checked.trans (by decide +kernel)
    · exact v2277_mg_checked.trans (by decide +kernel)
  upper_error := v2277_upper_checked
  lower_error := reuse_lower_error 27 37 Primitive.Addresses.material2277

def v2278_pa : Scalar.QComplex := ((999999771983159310425131653969 : Int)/10^30,(-675302620598698771728929112 : Int)/10^30)
theorem v2278_pa_checked : Scalar.distance (sourceCoefficient 27 38 1 0) v2278_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2278_pb : Scalar.QComplex := ((-291377899383935443604321 : Int)/10^30,(-431477420725159303391446921 : Int)/10^30)
theorem v2278_pb_checked : Scalar.distance (sourceCoefficient 27 38 1 1) v2278_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2278_pg : Scalar.QComplex := ((-93086408467683396402608 : Int)/10^30,(62861509913830392863 : Int)/10^30)
theorem v2278_pg_checked : Scalar.distance (sourceCoefficient 27 38 1 2) v2278_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2278_mb : Scalar.QComplex := ((-663723371954797565226760 : Int)/10^30,(-431477008620392080221682451 : Int)/10^30)
theorem v2278_mb_checked : Scalar.distance (sourceCoefficient 27 38 3 1) v2278_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2278_mg : Scalar.QComplex := ((-93086319560707386525094 : Int)/10^30,(143190864559022015535 : Int)/10^30)
theorem v2278_mg_checked : Scalar.distance (sourceCoefficient 27 38 3 2) v2278_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2278_upper : Scalar.QComplex := ((999997117089906988245755453498 : Int)/10^30,(-2401210501987050717982268536 : Int)/10^30)
theorem v2278_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 38 5) 1) 14) v2278_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2278 : Material (27 : Basis) (38 : Basis) where
  plus := ![v2278_pa,v2278_pb,v2278_pg]
  minus := ![(Primitive.Addresses.material2278 1).one,v2278_mb,v2278_mg]
  upper := v2278_upper
  lower := (Primitive.Addresses.material2278 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2278_pa_checked.trans (by decide +kernel)
    · exact v2278_pb_checked.trans (by decide +kernel)
    · exact v2278_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 38 Primitive.Addresses.material2278
    · exact v2278_mb_checked.trans (by decide +kernel)
    · exact v2278_mg_checked.trans (by decide +kernel)
  upper_error := v2278_upper_checked
  lower_error := reuse_lower_error 27 38 Primitive.Addresses.material2278

def v2279_pa : Scalar.QComplex := ((999999762763467981301734574630 : Int)/10^30,(-688820011146761332671528690 : Int)/10^30)
theorem v2279_pa_checked : Scalar.distance (sourceCoefficient 27 39 1 0) v2279_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2279_pb : Scalar.QComplex := ((-297210349296214634706832 : Int)/10^30,(-431477416418638114965632396 : Int)/10^30)
theorem v2279_pb_checked : Scalar.distance (sourceCoefficient 27 39 1 1) v2279_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2279_pg : Scalar.QComplex := ((-93086407574027528157577 : Int)/10^30,(64119795514311532052 : Int)/10^30)
theorem v2279_pg_checked : Scalar.distance (sourceCoefficient 27 39 1 2) v2279_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2279_mb : Scalar.QComplex := ((-669555815979055270761367 : Int)/10^30,(-431476999280730904806350501 : Int)/10^30)
theorem v2279_mb_checked : Scalar.distance (sourceCoefficient 27 39 3 1) v2279_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2279_mg : Scalar.QComplex := ((-93086317581208048893478 : Int)/10^30,(144449148919801153642 : Int)/10^30)
theorem v2279_mg_checked : Scalar.distance (sourceCoefficient 27 39 3 2) v2279_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2279_upper : Scalar.QComplex := ((999997084540439592904875254467 : Int)/10^30,(-2414727856490197091617604192 : Int)/10^30)
theorem v2279_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 39 5) 1) 14) v2279_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2279 : Material (27 : Basis) (39 : Basis) where
  plus := ![v2279_pa,v2279_pb,v2279_pg]
  minus := ![(Primitive.Addresses.material2279 1).one,v2279_mb,v2279_mg]
  upper := v2279_upper
  lower := (Primitive.Addresses.material2279 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2279_pa_checked.trans (by decide +kernel)
    · exact v2279_pb_checked.trans (by decide +kernel)
    · exact v2279_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 39 Primitive.Addresses.material2279
    · exact v2279_mb_checked.trans (by decide +kernel)
    · exact v2279_mg_checked.trans (by decide +kernel)
  upper_error := v2279_upper_checked
  lower_error := reuse_lower_error 27 39 Primitive.Addresses.material2279

def v2280_pa : Scalar.QComplex := ((999999746844350162274998332949 : Int)/10^30,(-711555504221327036860557769 : Int)/10^30)
theorem v2280_pa_checked : Scalar.distance (sourceCoefficient 27 40 1 0) v2280_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2280_pb : Scalar.QComplex := ((-307020203001046173646914 : Int)/10^30,(-431477408938220444450746559 : Int)/10^30)
theorem v2280_pb_checked : Scalar.distance (sourceCoefficient 27 40 1 1) v2280_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2280_pg : Scalar.QComplex := ((-93086406026192550566357 : Int)/10^30,(66236161344177083779 : Int)/10^30)
theorem v2280_pg_checked : Scalar.distance (sourceCoefficient 27 40 1 2) v2280_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2280_mb : Scalar.QComplex := ((-679365659575966398781296 : Int)/10^30,(-431476983334854091732975449 : Int)/10^30)
theorem v2280_mb_checked : Scalar.distance (sourceCoefficient 27 40 3 1) v2280_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2280_mg : Scalar.QComplex := ((-93086314207045254036611 : Int)/10^30,(146565512625935110451 : Int)/10^30)
theorem v2280_mg_checked : Scalar.distance (sourceCoefficient 27 40 3 2) v2280_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2280_upper : Scalar.QComplex := ((999997029381946984653719301420 : Int)/10^30,(-2437463288227963375311051213 : Int)/10^30)
theorem v2280_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 40 5) 1) 14) v2280_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2280 : Material (27 : Basis) (40 : Basis) where
  plus := ![v2280_pa,v2280_pb,v2280_pg]
  minus := ![(Primitive.Addresses.material2280 1).one,v2280_mb,v2280_mg]
  upper := v2280_upper
  lower := (Primitive.Addresses.material2280 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2280_pa_checked.trans (by decide +kernel)
    · exact v2280_pb_checked.trans (by decide +kernel)
    · exact v2280_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 40 Primitive.Addresses.material2280
    · exact v2280_mb_checked.trans (by decide +kernel)
    · exact v2280_mg_checked.trans (by decide +kernel)
  upper_error := v2280_upper_checked
  lower_error := reuse_lower_error 27 40 Primitive.Addresses.material2280

def v2281_pa : Scalar.QComplex := ((999999736433291234543524706854 : Int)/10^30,(-726039494837231964980671067 : Int)/10^30)
theorem v2281_pa_checked : Scalar.distance (sourceCoefficient 27 41 1 0) v2281_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2281_pb : Scalar.QComplex := ((-313269719014114688023148 : Int)/10^30,(-431477404017637664189040753 : Int)/10^30)
theorem v2281_pb_checked : Scalar.distance (sourceCoefficient 27 41 1 1) v2281_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2281_pg : Scalar.QComplex := ((-93086405010848157735865 : Int)/10^30,(67584424283294446890 : Int)/10^30)
theorem v2281_pg_checked : Scalar.distance (sourceCoefficient 27 41 1 2) v2281_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2281_mb : Scalar.QComplex := ((-685615169015813159956401 : Int)/10^30,(-431476973021222292103647058 : Int)/10^30)
theorem v2281_mb_checked : Scalar.distance (sourceCoefficient 27 41 3 1) v2281_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2281_mg : Scalar.QComplex := ((-93086312028211046315571 : Int)/10^30,(147913774186836081070 : Int)/10^30)
theorem v2281_mg_checked : Scalar.distance (sourceCoefficient 27 41 3 2) v2281_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2281_upper : Scalar.QComplex := ((999996993972849737284090713842 : Int)/10^30,(-2451947239303122464719482813 : Int)/10^30)
theorem v2281_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 41 5) 1) 14) v2281_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2281 : Material (27 : Basis) (41 : Basis) where
  plus := ![v2281_pa,v2281_pb,v2281_pg]
  minus := ![(Primitive.Addresses.material2281 1).one,v2281_mb,v2281_mg]
  upper := v2281_upper
  lower := (Primitive.Addresses.material2281 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2281_pa_checked.trans (by decide +kernel)
    · exact v2281_pb_checked.trans (by decide +kernel)
    · exact v2281_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 41 Primitive.Addresses.material2281
    · exact v2281_mb_checked.trans (by decide +kernel)
    · exact v2281_mg_checked.trans (by decide +kernel)
  upper_error := v2281_upper_checked
  lower_error := reuse_lower_error 27 41 Primitive.Addresses.material2281

def v2282_pa : Scalar.QComplex := ((999999727882246110933639061211 : Int)/10^30,(-737723141652788834518174418 : Int)/10^30)
theorem v2282_pa_checked : Scalar.distance (sourceCoefficient 27 42 1 0) v2282_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2282_pb : Scalar.QComplex := ((-318310949669067118531935 : Int)/10^30,(-431477399960458644808350668 : Int)/10^30)
theorem v2282_pb_checked : Scalar.distance (sourceCoefficient 27 42 1 1) v2282_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2282_pg : Scalar.QComplex := ((-93086404175209620065300 : Int)/10^30,(68672013220170913052 : Int)/10^30)
theorem v2282_pg_checked : Scalar.distance (sourceCoefficient 27 42 1 2) v2282_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2282_mb : Scalar.QComplex := ((-690656394292522256837987 : Int)/10^30,(-431476964613689776772439435 : Int)/10^30)
theorem v2282_mb_checked : Scalar.distance (sourceCoefficient 27 42 3 1) v2282_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2282_mg : Scalar.QComplex := ((-93086310254032550454410 : Int)/10^30,(149001361997635058516 : Int)/10^30)
theorem v2282_mg_checked : Scalar.distance (sourceCoefficient 27 42 3 2) v2282_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2282_upper : Scalar.QComplex := ((999996965256902877959655211326 : Int)/10^30,(-2463630853958931721453035688 : Int)/10^30)
theorem v2282_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 42 5) 1) 14) v2282_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2282 : Material (27 : Basis) (42 : Basis) where
  plus := ![v2282_pa,v2282_pb,v2282_pg]
  minus := ![(Primitive.Addresses.material2282 1).one,v2282_mb,v2282_mg]
  upper := v2282_upper
  lower := (Primitive.Addresses.material2282 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2282_pa_checked.trans (by decide +kernel)
    · exact v2282_pb_checked.trans (by decide +kernel)
    · exact v2282_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 42 Primitive.Addresses.material2282
    · exact v2282_mb_checked.trans (by decide +kernel)
    · exact v2282_mg_checked.trans (by decide +kernel)
  upper_error := v2282_upper_checked
  lower_error := reuse_lower_error 27 42 Primitive.Addresses.material2282

def v2283_pa : Scalar.QComplex := ((999999716344142419998697609197 : Int)/10^30,(-753200925848712074812780302 : Int)/10^30)
theorem v2283_pa_checked : Scalar.distance (sourceCoefficient 27 43 1 0) v2283_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2283_pb : Scalar.QComplex := ((-324989265178805860882510 : Int)/10^30,(-431477394464826324533288194 : Int)/10^30)
theorem v2283_pb_checked : Scalar.distance (sourceCoefficient 27 43 1 1) v2283_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2283_pg : Scalar.QComplex := ((-93086403045378700236864 : Int)/10^30,(70112784845607720962 : Int)/10^30)
theorem v2283_pg_checked : Scalar.distance (sourceCoefficient 27 43 1 2) v2283_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2283_mb : Scalar.QComplex := ((-697334702573135742510322 : Int)/10^30,(-431476953354973998032992022 : Int)/10^30)
theorem v2283_mb_checked : Scalar.distance (sourceCoefficient 27 43 3 1) v2283_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2283_mg : Scalar.QComplex := ((-93086307880881028506878 : Int)/10^30,(150442132111613545644 : Int)/10^30)
theorem v2283_mg_checked : Scalar.distance (sourceCoefficient 27 43 3 2) v2283_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2283_upper : Scalar.QComplex := ((999996927005564983125052088682 : Int)/10^30,(-2479108595188793308206114548 : Int)/10^30)
theorem v2283_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 43 5) 1) 14) v2283_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2283 : Material (27 : Basis) (43 : Basis) where
  plus := ![v2283_pa,v2283_pb,v2283_pg]
  minus := ![(Primitive.Addresses.material2283 1).one,v2283_mb,v2283_mg]
  upper := v2283_upper
  lower := (Primitive.Addresses.material2283 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2283_pa_checked.trans (by decide +kernel)
    · exact v2283_pb_checked.trans (by decide +kernel)
    · exact v2283_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 43 Primitive.Addresses.material2283
    · exact v2283_mb_checked.trans (by decide +kernel)
    · exact v2283_mg_checked.trans (by decide +kernel)
  upper_error := v2283_upper_checked
  lower_error := reuse_lower_error 27 43 Primitive.Addresses.material2283

def v2284_pa : Scalar.QComplex := ((999999711916418863722242572107 : Int)/10^30,(-759056703600202581435614250 : Int)/10^30)
theorem v2284_pa_checked : Scalar.distance (sourceCoefficient 27 44 1 0) v2284_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2284_pb : Scalar.QComplex := ((-327515901466932067444446 : Int)/10^30,(-431477392349704932458741515 : Int)/10^30)
theorem v2284_pb_checked : Scalar.distance (sourceCoefficient 27 44 1 1) v2284_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2284_pg : Scalar.QComplex := ((-93086402611141366850550 : Int)/10^30,(70657878271388864045 : Int)/10^30)
theorem v2284_pg_checked : Scalar.distance (sourceCoefficient 27 44 1 2) v2284_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2284_mb : Scalar.QComplex := ((-699861336095225286190914 : Int)/10^30,(-431476949059480072336019813 : Int)/10^30)
theorem v2284_mb_checked : Scalar.distance (sourceCoefficient 27 44 3 1) v2284_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2284_mg : Scalar.QComplex := ((-93086306976252780454396 : Int)/10^30,(150987224959704232919 : Int)/10^30)
theorem v2284_mg_checked : Scalar.distance (sourceCoefficient 27 44 3 2) v2284_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2284_upper : Scalar.QComplex := ((999996912471306854357961254560 : Int)/10^30,(-2484964356576941543768731218 : Int)/10^30)
theorem v2284_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 44 5) 1) 14) v2284_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2284 : Material (27 : Basis) (44 : Basis) where
  plus := ![v2284_pa,v2284_pb,v2284_pg]
  minus := ![(Primitive.Addresses.material2284 1).one,v2284_mb,v2284_mg]
  upper := v2284_upper
  lower := (Primitive.Addresses.material2284 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2284_pa_checked.trans (by decide +kernel)
    · exact v2284_pb_checked.trans (by decide +kernel)
    · exact v2284_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 44 Primitive.Addresses.material2284
    · exact v2284_mb_checked.trans (by decide +kernel)
    · exact v2284_mg_checked.trans (by decide +kernel)
  upper_error := v2284_upper_checked
  lower_error := reuse_lower_error 27 44 Primitive.Addresses.material2284

def v2285_pa : Scalar.QComplex := ((999999709700797450005631774107 : Int)/10^30,(-761970026199431112037835147 : Int)/10^30)
theorem v2285_pa_checked : Scalar.distance (sourceCoefficient 27 45 1 0) v2285_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2285_pb : Scalar.QComplex := ((-328772934588267581438346 : Int)/10^30,(-431477391290056906357424389 : Int)/10^30)
theorem v2285_pb_checked : Scalar.distance (sourceCoefficient 27 45 1 1) v2285_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2285_pg : Scalar.QComplex := ((-93086402393715642049824 : Int)/10^30,(70929069061402480893 : Int)/10^30)
theorem v2285_pg_checked : Scalar.distance (sourceCoefficient 27 45 1 2) v2285_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2285_mb : Scalar.QComplex := ((-701118367834081398109938 : Int)/10^30,(-431476946915069471747692142 : Int)/10^30)
theorem v2285_mb_checked : Scalar.distance (sourceCoefficient 27 45 3 1) v2285_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2285_mg : Scalar.QComplex := ((-93086306524801698809231 : Int)/10^30,(151258415461112516602 : Int)/10^30)
theorem v2285_mg_checked : Scalar.distance (sourceCoefficient 27 45 3 2) v2285_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2285_upper : Scalar.QComplex := ((999996905227558228842383390350 : Int)/10^30,(-2487877671013156725262068979 : Int)/10^30)
theorem v2285_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 45 5) 1) 14) v2285_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2285 : Material (27 : Basis) (45 : Basis) where
  plus := ![v2285_pa,v2285_pb,v2285_pg]
  minus := ![(Primitive.Addresses.material2285 1).one,v2285_mb,v2285_mg]
  upper := v2285_upper
  lower := (Primitive.Addresses.material2285 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2285_pa_checked.trans (by decide +kernel)
    · exact v2285_pb_checked.trans (by decide +kernel)
    · exact v2285_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 45 Primitive.Addresses.material2285
    · exact v2285_mb_checked.trans (by decide +kernel)
    · exact v2285_mg_checked.trans (by decide +kernel)
  upper_error := v2285_upper_checked
  lower_error := reuse_lower_error 27 45 Primitive.Addresses.material2285

def v2286_pa : Scalar.QComplex := ((999999697097840413251683919768 : Int)/10^30,(-778334264582883662889063287 : Int)/10^30)
theorem v2286_pa_checked : Scalar.distance (sourceCoefficient 27 46 1 0) v2286_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2286_pb : Scalar.QComplex := ((-335833735055313675744562 : Int)/10^30,(-431477385247232218263854064 : Int)/10^30)
theorem v2286_pb_checked : Scalar.distance (sourceCoefficient 27 46 1 1) v2286_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2286_pg : Scalar.QComplex := ((-93086401155297719761639 : Int)/10^30,(72452357531851506431 : Int)/10^30)
theorem v2286_pg_checked : Scalar.distance (sourceCoefficient 27 46 1 2) v2286_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2286_mb : Scalar.QComplex := ((-708179160457383236908310 : Int)/10^30,(-431476934779094237261218622 : Int)/10^30)
theorem v2286_mb_checked : Scalar.distance (sourceCoefficient 27 46 3 1) v2286_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2286_mg : Scalar.QComplex := ((-93086303971854894009049 : Int)/10^30,(152781702295672736207 : Int)/10^30)
theorem v2286_mg_checked : Scalar.distance (sourceCoefficient 27 46 3 2) v2286_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2286_upper : Scalar.QComplex := ((999996864381429064982853826199 : Int)/10^30,(-2504241863272437968327786916 : Int)/10^30)
theorem v2286_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 46 5) 1) 14) v2286_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2286 : Material (27 : Basis) (46 : Basis) where
  plus := ![v2286_pa,v2286_pb,v2286_pg]
  minus := ![(Primitive.Addresses.material2286 1).one,v2286_mb,v2286_mg]
  upper := v2286_upper
  lower := (Primitive.Addresses.material2286 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2286_pa_checked.trans (by decide +kernel)
    · exact v2286_pb_checked.trans (by decide +kernel)
    · exact v2286_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 46 Primitive.Addresses.material2286
    · exact v2286_mb_checked.trans (by decide +kernel)
    · exact v2286_mg_checked.trans (by decide +kernel)
  upper_error := v2286_upper_checked
  lower_error := reuse_lower_error 27 46 Primitive.Addresses.material2286

def v2287_pa : Scalar.QComplex := ((999999694024972753903659104701 : Int)/10^30,(-782272306087512843343287781 : Int)/10^30)
theorem v2287_pa_checked : Scalar.distance (sourceCoefficient 27 47 1 0) v2287_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2287_pb : Scalar.QComplex := ((-337532911303032186898419 : Int)/10^30,(-431477383770032940175294139 : Int)/10^30)
theorem v2287_pb_checked : Scalar.distance (sourceCoefficient 27 47 1 1) v2287_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2287_pg : Scalar.QComplex := ((-93086400852932001847643 : Int)/10^30,(72818935741385587064 : Int)/10^30)
theorem v2287_pg_checked : Scalar.distance (sourceCoefficient 27 47 1 2) v2287_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2287_mb : Scalar.QComplex := ((-709878334797664328441078 : Int)/10^30,(-431476931835582935477728363 : Int)/10^30)
theorem v2287_mb_checked : Scalar.distance (sourceCoefficient 27 47 3 1) v2287_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2287_mg : Scalar.QComplex := ((-93086303353148803921392 : Int)/10^30,(153148280107784999466 : Int)/10^30)
theorem v2287_mg_checked : Scalar.distance (sourceCoefficient 27 47 3 2) v2287_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2287_upper : Scalar.QComplex := ((999996854511863601654844378964 : Int)/10^30,(-2508179893608326110829242940 : Int)/10^30)
theorem v2287_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 47 5) 1) 14) v2287_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2287 : Material (27 : Basis) (47 : Basis) where
  plus := ![v2287_pa,v2287_pb,v2287_pg]
  minus := ![(Primitive.Addresses.material2287 1).one,v2287_mb,v2287_mg]
  upper := v2287_upper
  lower := (Primitive.Addresses.material2287 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2287_pa_checked.trans (by decide +kernel)
    · exact v2287_pb_checked.trans (by decide +kernel)
    · exact v2287_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 47 Primitive.Addresses.material2287
    · exact v2287_mb_checked.trans (by decide +kernel)
    · exact v2287_mg_checked.trans (by decide +kernel)
  upper_error := v2287_upper_checked
  lower_error := reuse_lower_error 27 47 Primitive.Addresses.material2287

def v2288_pa : Scalar.QComplex := ((999999672190581297851961578652 : Int)/10^30,(-809702865219878721779096580 : Int)/10^30)
theorem v2288_pa_checked : Scalar.distance (sourceCoefficient 27 48 1 0) v2288_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2288_pb : Scalar.QComplex := ((-349368579910650407178951 : Int)/10^30,(-431477373233039777586316418 : Int)/10^30)
theorem v2288_pb_checked : Scalar.distance (sourceCoefficient 27 48 1 1) v2288_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2288_pg : Scalar.QComplex := ((-93086398700070252787360 : Int)/10^30,(75372348448212608769 : Int)/10^30)
theorem v2288_pg_checked : Scalar.distance (sourceCoefficient 27 48 1 2) v2288_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2288_mb : Scalar.QComplex := ((-721713989905371678569090 : Int)/10^30,(-431476911084944746644362418 : Int)/10^30)
theorem v2288_mb_checked : Scalar.distance (sourceCoefficient 27 48 3 1) v2288_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2288_mg : Scalar.QComplex := ((-93086298996807691917471 : Int)/10^30,(155701690006037045548 : Int)/10^30)
theorem v2288_mg_checked : Scalar.distance (sourceCoefficient 27 48 3 2) v2288_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2288_upper : Scalar.QComplex := ((999996785334848083786409003267 : Int)/10^30,(-2535610374201917528804859335 : Int)/10^30)
theorem v2288_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 48 5) 1) 14) v2288_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2288 : Material (27 : Basis) (48 : Basis) where
  plus := ![v2288_pa,v2288_pb,v2288_pg]
  minus := ![(Primitive.Addresses.material2288 1).one,v2288_mb,v2288_mg]
  upper := v2288_upper
  lower := (Primitive.Addresses.material2288 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2288_pa_checked.trans (by decide +kernel)
    · exact v2288_pb_checked.trans (by decide +kernel)
    · exact v2288_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 48 Primitive.Addresses.material2288
    · exact v2288_mb_checked.trans (by decide +kernel)
    · exact v2288_mg_checked.trans (by decide +kernel)
  upper_error := v2288_upper_checked
  lower_error := reuse_lower_error 27 48 Primitive.Addresses.material2288

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
