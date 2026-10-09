import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B175
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B176

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4209_pa : Scalar.QComplex := ((999998244909963317765425017299 : Int)/10^30,(-1873546634867526399656538727 : Int)/10^30)
theorem v4209_pa_checked : Scalar.distance (sourceCoefficient 64 82 1 0) v4209_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4209_pb : Scalar.QComplex := ((-808393242215863200197623 : Int)/10^30,(-431476755565306408912522915 : Int)/10^30)
theorem v4209_pb_checked : Scalar.distance (sourceCoefficient 64 82 1 1) v4209_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4209_pg : Scalar.QComplex := ((-93086265642402959446296 : Int)/10^30,(174401765837510306435 : Int)/10^30)
theorem v4209_pg_checked : Scalar.distance (sourceCoefficient 64 82 1 2) v4209_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4209_mb : Scalar.QComplex := ((-1180737948275289056798509 : Int)/10^30,(-431475897299831497844156197 : Int)/10^30)
theorem v4209_mb_checked : Scalar.distance (sourceCoefficient 64 82 3 1) v4209_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4209_mg : Scalar.QComplex := ((-93086080481262854454862 : Int)/10^30,(254730955699382601944 : Int)/10^30)
theorem v4209_mg_checked : Scalar.distance (sourceCoefficient 64 82 3 2) v4209_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4209_upper : Scalar.QComplex := ((999993521958520611558984226788 : Int)/10^30,(-3599450096022373436784613921 : Int)/10^30)
theorem v4209_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 64 82 5) 1) 14) v4209_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4209 : Material (64 : Basis) (82 : Basis) where
  plus := ![v4209_pa,v4209_pb,v4209_pg]
  minus := ![(Primitive.Addresses.material4209 1).one,v4209_mb,v4209_mg]
  upper := v4209_upper
  lower := (Primitive.Addresses.material4209 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4209_pa_checked.trans (by decide +kernel)
    · exact v4209_pb_checked.trans (by decide +kernel)
    · exact v4209_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 64 82 Primitive.Addresses.material4209
    · exact v4209_mb_checked.trans (by decide +kernel)
    · exact v4209_mg_checked.trans (by decide +kernel)
  upper_error := v4209_upper_checked
  lower_error := reuse_lower_error 64 82 Primitive.Addresses.material4209

def v4210_pa : Scalar.QComplex := ((999998219396465869891701676670 : Int)/10^30,(-1887115231699238561369540995 : Int)/10^30)
theorem v4210_pa_checked : Scalar.distance (sourceCoefficient 64 83 1 0) v4210_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4210_pb : Scalar.QComplex := ((-814247785364603426659461 : Int)/10^30,(-431476743886454261347196370 : Int)/10^30)
theorem v4210_pb_checked : Scalar.distance (sourceCoefficient 64 83 1 1) v4210_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4210_pg : Scalar.QComplex := ((-93086263195132162204938 : Int)/10^30,(175664817926893756064 : Int)/10^30)
theorem v4210_pg_checked : Scalar.distance (sourceCoefficient 64 83 1 2) v4210_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4210_mb : Scalar.QComplex := ((-1186592479165791895770403 : Int)/10^30,(-431475880568776640321619463 : Int)/10^30)
theorem v4210_mb_checked : Scalar.distance (sourceCoefficient 64 83 3 1) v4210_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4210_mg : Scalar.QComplex := ((-93086076944035901060758 : Int)/10^30,(255994005206589557329 : Int)/10^30)
theorem v4210_mg_checked : Scalar.distance (sourceCoefficient 64 83 3 2) v4210_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4210_upper : Scalar.QComplex := ((999993473026893964996540633005 : Int)/10^30,(-3613018628611272468388145793 : Int)/10^30)
theorem v4210_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 64 83 5) 1) 14) v4210_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4210 : Material (64 : Basis) (83 : Basis) where
  plus := ![v4210_pa,v4210_pb,v4210_pg]
  minus := ![(Primitive.Addresses.material4210 1).one,v4210_mb,v4210_mg]
  upper := v4210_upper
  lower := (Primitive.Addresses.material4210 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4210_pa_checked.trans (by decide +kernel)
    · exact v4210_pb_checked.trans (by decide +kernel)
    · exact v4210_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 64 83 Primitive.Addresses.material4210
    · exact v4210_mb_checked.trans (by decide +kernel)
    · exact v4210_mg_checked.trans (by decide +kernel)
  upper_error := v4210_upper_checked
  lower_error := reuse_lower_error 64 83 Primitive.Addresses.material4210

def v4211_pa : Scalar.QComplex := ((999998152467640268743668110767 : Int)/10^30,(-1922254225144710771701690997 : Int)/10^30)
theorem v4211_pa_checked : Scalar.distance (sourceCoefficient 64 84 1 0) v4211_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4211_pb : Scalar.QComplex := ((-829409467263162923433254 : Int)/10^30,(-431476713149059854008930791 : Int)/10^30)
theorem v4211_pb_checked : Scalar.distance (sourceCoefficient 64 84 1 1) v4211_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4211_pg : Scalar.QComplex := ((-93086256764425607416769 : Int)/10^30,(178935780957968171236 : Int)/10^30)
theorem v4211_pg_checked : Scalar.distance (sourceCoefficient 64 84 1 2) v4211_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4211_mb : Scalar.QComplex := ((-1201754128893977285937929 : Int)/10^30,(-431475836747545056267089369 : Int)/10^30)
theorem v4211_mb_checked : Scalar.distance (sourceCoefficient 64 84 3 1) v4211_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4211_mg : Scalar.QComplex := ((-93086067690637963607509 : Int)/10^30,(259264961470324817126 : Int)/10^30)
theorem v4211_mg_checked : Scalar.distance (sourceCoefficient 64 84 3 2) v4211_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4211_upper : Scalar.QComplex := ((999993345451453144170959443112 : Int)/10^30,(-3648157454208260405863021256 : Int)/10^30)
theorem v4211_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 64 84 5) 1) 14) v4211_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4211 : Material (64 : Basis) (84 : Basis) where
  plus := ![v4211_pa,v4211_pb,v4211_pg]
  minus := ![(Primitive.Addresses.material4211 1).one,v4211_mb,v4211_mg]
  upper := v4211_upper
  lower := (Primitive.Addresses.material4211 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4211_pa_checked.trans (by decide +kernel)
    · exact v4211_pb_checked.trans (by decide +kernel)
    · exact v4211_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 64 84 Primitive.Addresses.material4211
    · exact v4211_mb_checked.trans (by decide +kernel)
    · exact v4211_mg_checked.trans (by decide +kernel)
  upper_error := v4211_upper_checked
  lower_error := reuse_lower_error 64 84 Primitive.Addresses.material4211

def v4212_pa : Scalar.QComplex := ((999997997375354648337897870069 : Int)/10^30,(-2001310890441026414990163929 : Int)/10^30)
theorem v4212_pa_checked : Scalar.distance (sourceCoefficient 64 85 1 0) v4212_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4212_pb : Scalar.QComplex := ((-863520630709075670874501 : Int)/10^30,(-431476641398321800447685078 : Int)/10^30)
theorem v4212_pb_checked : Scalar.distance (sourceCoefficient 64 85 1 1) v4212_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4212_pg : Scalar.QComplex := ((-93086241806224016060752 : Int)/10^30,(186294882555745993661 : Int)/10^30)
theorem v4212_pg_checked : Scalar.distance (sourceCoefficient 64 85 1 2) v4212_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4212_mb : Scalar.QComplex := ((-1235865217721089518340758 : Int)/10^30,(-431475735560435974733195142 : Int)/10^30)
theorem v4212_mb_checked : Scalar.distance (sourceCoefficient 64 85 3 1) v4212_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4212_mg : Scalar.QComplex := ((-93086046381868704623579 : Int)/10^30,(266624047419718506191 : Int)/10^30)
theorem v4212_mg_checked : Scalar.distance (sourceCoefficient 64 85 3 2) v4212_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4212_upper : Scalar.QComplex := ((999993053914766178716769260605 : Int)/10^30,(-3727213734083744619969900081 : Int)/10^30)
theorem v4212_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 64 85 5) 1) 14) v4212_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4212 : Material (64 : Basis) (85 : Basis) where
  plus := ![v4212_pa,v4212_pb,v4212_pg]
  minus := ![(Primitive.Addresses.material4212 1).one,v4212_mb,v4212_mg]
  upper := v4212_upper
  lower := (Primitive.Addresses.material4212 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4212_pa_checked.trans (by decide +kernel)
    · exact v4212_pb_checked.trans (by decide +kernel)
    · exact v4212_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 64 85 Primitive.Addresses.material4212
    · exact v4212_mb_checked.trans (by decide +kernel)
    · exact v4212_mg_checked.trans (by decide +kernel)
  upper_error := v4212_upper_checked
  lower_error := reuse_lower_error 64 85 Primitive.Addresses.material4212

def v4213_pa : Scalar.QComplex := ((999997968080591868853889168256 : Int)/10^30,(-2015895505120692281771272092 : Int)/10^30)
theorem v4213_pa_checked : Scalar.distance (sourceCoefficient 64 86 1 0) v4213_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4213_pb : Scalar.QComplex := ((-869813561874559418677200 : Int)/10^30,(-431476627768672806947905425 : Int)/10^30)
theorem v4213_pb_checked : Scalar.distance (sourceCoefficient 64 86 1 1) v4213_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4213_pg : Scalar.QComplex := ((-93086238972529716966848 : Int)/10^30,(187652512028094439944 : Int)/10^30)
theorem v4213_pg_checked : Scalar.distance (sourceCoefficient 64 86 1 2) v4213_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4213_mb : Scalar.QComplex := ((-1242158134781654167284739 : Int)/10^30,(-431475716500275883460700567 : Int)/10^30)
theorem v4213_mb_checked : Scalar.distance (sourceCoefficient 64 86 3 1) v4213_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4213_mg : Scalar.QComplex := ((-93086042376602371368472 : Int)/10^30,(267981673941208897922 : Int)/10^30)
theorem v4213_mg_checked : Scalar.distance (sourceCoefficient 64 86 3 2) v4213_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4213_upper : Scalar.QComplex := ((999992999448325199145633098664 : Int)/10^30,(-3741798276481237193306682656 : Int)/10^30)
theorem v4213_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 64 86 5) 1) 14) v4213_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4213 : Material (64 : Basis) (86 : Basis) where
  plus := ![v4213_pa,v4213_pb,v4213_pg]
  minus := ![(Primitive.Addresses.material4213 1).one,v4213_mb,v4213_mg]
  upper := v4213_upper
  lower := (Primitive.Addresses.material4213 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4213_pa_checked.trans (by decide +kernel)
    · exact v4213_pb_checked.trans (by decide +kernel)
    · exact v4213_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 64 86 Primitive.Addresses.material4213
    · exact v4213_mb_checked.trans (by decide +kernel)
    · exact v4213_mg_checked.trans (by decide +kernel)
  upper_error := v4213_upper_checked
  lower_error := reuse_lower_error 64 86 Primitive.Addresses.material4213

def v4214_pa : Scalar.QComplex := ((999997966133261459775256400307 : Int)/10^30,(-2016861259597828495844757933 : Int)/10^30)
theorem v4214_pa_checked : Scalar.distance (sourceCoefficient 64 87 1 0) v4214_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4214_pb : Scalar.QComplex := ((-870230263071967083083147 : Int)/10^30,(-431476626861833695954143120 : Int)/10^30)
theorem v4214_pb_checked : Scalar.distance (sourceCoefficient 64 87 1 1) v4214_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4214_pg : Scalar.QComplex := ((-93086238784074521730808 : Int)/10^30,(187742410648317206136 : Int)/10^30)
theorem v4214_pg_checked : Scalar.distance (sourceCoefficient 64 87 1 2) v4214_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4214_mb : Scalar.QComplex := ((-1242574835041343621440086 : Int)/10^30,(-431475715233842744287017453 : Int)/10^30)
theorem v4214_mb_checked : Scalar.distance (sourceCoefficient 64 87 3 1) v4214_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4214_mg : Scalar.QComplex := ((-93086042110568785934220 : Int)/10^30,(268071572365329953454 : Int)/10^30)
theorem v4214_mg_checked : Scalar.distance (sourceCoefficient 64 87 3 2) v4214_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4214_upper : Scalar.QComplex := ((999992995834193075411563686957 : Int)/10^30,(-3742764026159079933540768950 : Int)/10^30)
theorem v4214_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 64 87 5) 1) 14) v4214_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4214 : Material (64 : Basis) (87 : Basis) where
  plus := ![v4214_pa,v4214_pb,v4214_pg]
  minus := ![(Primitive.Addresses.material4214 1).one,v4214_mb,v4214_mg]
  upper := v4214_upper
  lower := (Primitive.Addresses.material4214 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4214_pa_checked.trans (by decide +kernel)
    · exact v4214_pb_checked.trans (by decide +kernel)
    · exact v4214_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 64 87 Primitive.Addresses.material4214
    · exact v4214_mb_checked.trans (by decide +kernel)
    · exact v4214_mg_checked.trans (by decide +kernel)
  upper_error := v4214_upper_checked
  lower_error := reuse_lower_error 64 87 Primitive.Addresses.material4214

def v4215_pa : Scalar.QComplex := ((999997942346648910068632439044 : Int)/10^30,(-2028620829096100325135800965 : Int)/10^30)
theorem v4215_pa_checked : Scalar.distance (sourceCoefficient 64 88 1 0) v4215_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4215_pb : Scalar.QComplex := ((-875304251105041810517570 : Int)/10^30,(-431476615776605169571045580 : Int)/10^30)
theorem v4215_pb_checked : Scalar.distance (sourceCoefficient 64 88 1 1) v4215_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4215_pg : Scalar.QComplex := ((-93086236481212314334070 : Int)/10^30,(188837066789175874362 : Int)/10^30)
theorem v4215_pg_checked : Scalar.distance (sourceCoefficient 64 88 1 2) v4215_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4215_mb : Scalar.QComplex := ((-1247648811619087753342750 : Int)/10^30,(-431475699769995196835432839 : Int)/10^30)
theorem v4215_mb_checked : Scalar.distance (sourceCoefficient 64 88 3 1) v4215_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4215_mg : Scalar.QComplex := ((-93086038863068487919724 : Int)/10^30,(269166226111331744261 : Int)/10^30)
theorem v4215_mg_checked : Scalar.distance (sourceCoefficient 64 88 3 2) v4215_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4215_upper : Scalar.QComplex := ((999992951751665818864327552767 : Int)/10^30,(-3754523537089319015065816139 : Int)/10^30)
theorem v4215_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 64 88 5) 1) 14) v4215_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4215 : Material (64 : Basis) (88 : Basis) where
  plus := ![v4215_pa,v4215_pb,v4215_pg]
  minus := ![(Primitive.Addresses.material4215 1).one,v4215_mb,v4215_mg]
  upper := v4215_upper
  lower := (Primitive.Addresses.material4215 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4215_pa_checked.trans (by decide +kernel)
    · exact v4215_pb_checked.trans (by decide +kernel)
    · exact v4215_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 64 88 Primitive.Addresses.material4215
    · exact v4215_mb_checked.trans (by decide +kernel)
    · exact v4215_mg_checked.trans (by decide +kernel)
  upper_error := v4215_upper_checked
  lower_error := reuse_lower_error 64 88 Primitive.Addresses.material4215

def v4216_pa : Scalar.QComplex := ((999997909577749979948151527077 : Int)/10^30,(-2044710280253640314750447480 : Int)/10^30)
theorem v4216_pa_checked : Scalar.distance (sourceCoefficient 64 89 1 0) v4216_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4216_pb : Scalar.QComplex := ((-882246484959866113297099 : Int)/10^30,(-431476600480897513978615302 : Int)/10^30)
theorem v4216_pb_checked : Scalar.distance (sourceCoefficient 64 89 1 1) v4216_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4216_pg : Scalar.QComplex := ((-93086233306103825836407 : Int)/10^30,(190334776071130152624 : Int)/10^30)
theorem v4216_pg_checked : Scalar.distance (sourceCoefficient 64 89 1 2) v4216_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4216_mb : Scalar.QComplex := ((-1254591029689494302533912 : Int)/10^30,(-431475678483458086426729102 : Int)/10^30)
theorem v4216_mb_checked : Scalar.distance (sourceCoefficient 64 89 3 1) v4216_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4216_mg : Scalar.QComplex := ((-93086034395505525655556 : Int)/10^30,(270663932095644784161 : Int)/10^30)
theorem v4216_mg_checked : Scalar.distance (sourceCoefficient 64 89 3 2) v4216_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4216_upper : Scalar.QComplex := ((999992891213882619862533843504 : Int)/10^30,(-3770612907727364723123825910 : Int)/10^30)
theorem v4216_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 64 89 5) 1) 14) v4216_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4216 : Material (64 : Basis) (89 : Basis) where
  plus := ![v4216_pa,v4216_pb,v4216_pg]
  minus := ![(Primitive.Addresses.material4216 1).one,v4216_mb,v4216_mg]
  upper := v4216_upper
  lower := (Primitive.Addresses.material4216 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4216_pa_checked.trans (by decide +kernel)
    · exact v4216_pb_checked.trans (by decide +kernel)
    · exact v4216_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 64 89 Primitive.Addresses.material4216
    · exact v4216_mb_checked.trans (by decide +kernel)
    · exact v4216_mg_checked.trans (by decide +kernel)
  upper_error := v4216_upper_checked
  lower_error := reuse_lower_error 64 89 Primitive.Addresses.material4216

def v4217_pa : Scalar.QComplex := ((999997855657029398352083620470 : Int)/10^30,(-2070913166454962752371677464 : Int)/10^30)
theorem v4217_pa_checked : Scalar.distance (sourceCoefficient 64 90 1 0) v4217_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4217_pb : Scalar.QComplex := ((-893552436788964218737178 : Int)/10^30,(-431476575251910758332542159 : Int)/10^30)
theorem v4217_pb_checked : Scalar.distance (sourceCoefficient 64 90 1 1) v4217_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4217_pg : Scalar.QComplex := ((-93086228075024845348452 : Int)/10^30,(192773908709574611322 : Int)/10^30)
theorem v4217_pg_checked : Scalar.distance (sourceCoefficient 64 90 1 2) v4217_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4217_mb : Scalar.QComplex := ((-1265896955537390535736844 : Int)/10^30,(-431475643497953497341728453 : Int)/10^30)
theorem v4217_mb_checked : Scalar.distance (sourceCoefficient 64 90 3 1) v4217_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4217_mg : Scalar.QComplex := ((-93086027059566880415856 : Int)/10^30,(273103059311703126587 : Int)/10^30)
theorem v4217_mg_checked : Scalar.distance (sourceCoefficient 64 90 3 2) v4217_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4217_upper : Scalar.QComplex := ((999992792069437870630513146732 : Int)/10^30,(-3796815661840294096831587347 : Int)/10^30)
theorem v4217_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 64 90 5) 1) 14) v4217_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4217 : Material (64 : Basis) (90 : Basis) where
  plus := ![v4217_pa,v4217_pb,v4217_pg]
  minus := ![(Primitive.Addresses.material4217 1).one,v4217_mb,v4217_mg]
  upper := v4217_upper
  lower := (Primitive.Addresses.material4217 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4217_pa_checked.trans (by decide +kernel)
    · exact v4217_pb_checked.trans (by decide +kernel)
    · exact v4217_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 64 90 Primitive.Addresses.material4217
    · exact v4217_mb_checked.trans (by decide +kernel)
    · exact v4217_mg_checked.trans (by decide +kernel)
  upper_error := v4217_upper_checked
  lower_error := reuse_lower_error 64 90 Primitive.Addresses.material4217

def v4218_pa : Scalar.QComplex := ((999997824979188764960536034342 : Int)/10^30,(-2085674205563886629907324260 : Int)/10^30)
theorem v4218_pa_checked : Scalar.distance (sourceCoefficient 64 91 1 0) v4218_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4218_pb : Scalar.QComplex := ((-899921490650705068300835 : Int)/10^30,(-431476560865569395852899315 : Int)/10^30)
theorem v4218_pb_checked : Scalar.distance (sourceCoefficient 64 91 1 1) v4218_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4218_pg : Scalar.QComplex := ((-93086225095333715469400 : Int)/10^30,(194147960850506582679 : Int)/10^30)
theorem v4218_pg_checked : Scalar.distance (sourceCoefficient 64 91 1 2) v4218_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4218_mb : Scalar.QComplex := ((-1272265994612876893375741 : Int)/10^30,(-431475623615410860409613170 : Int)/10^30)
theorem v4218_mb_checked : Scalar.distance (sourceCoefficient 64 91 3 1) v4218_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4218_mg : Scalar.QComplex := ((-93086022894131747398847 : Int)/10^30,(274477108369673443811 : Int)/10^30)
theorem v4218_mg_checked : Scalar.distance (sourceCoefficient 64 91 3 2) v4218_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4218_upper : Scalar.QComplex := ((999992735915428537283704508941 : Int)/10^30,(-3811576626017214313810724826 : Int)/10^30)
theorem v4218_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 64 91 5) 1) 14) v4218_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4218 : Material (64 : Basis) (91 : Basis) where
  plus := ![v4218_pa,v4218_pb,v4218_pg]
  minus := ![(Primitive.Addresses.material4218 1).one,v4218_mb,v4218_mg]
  upper := v4218_upper
  lower := (Primitive.Addresses.material4218 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4218_pa_checked.trans (by decide +kernel)
    · exact v4218_pb_checked.trans (by decide +kernel)
    · exact v4218_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 64 91 Primitive.Addresses.material4218
    · exact v4218_mb_checked.trans (by decide +kernel)
    · exact v4218_mg_checked.trans (by decide +kernel)
  upper_error := v4218_upper_checked
  lower_error := reuse_lower_error 64 91 Primitive.Addresses.material4218

def v4219_pa : Scalar.QComplex := ((999997757818570419613080534652 : Int)/10^30,(-2117630239627119294358978926 : Int)/10^30)
theorem v4219_pa_checked : Scalar.distance (sourceCoefficient 64 92 1 0) v4219_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4219_pb : Scalar.QComplex := ((-913709794819704447097947 : Int)/10^30,(-431476529291279741717652595 : Int)/10^30)
theorem v4219_pb_checked : Scalar.distance (sourceCoefficient 64 92 1 1) v4219_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4219_pg : Scalar.QComplex := ((-93086218563563404022729 : Int)/10^30,(197122633307448923599 : Int)/10^30)
theorem v4219_pg_checked : Scalar.distance (sourceCoefficient 64 92 1 2) v4219_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4219_mb : Scalar.QComplex := ((-1286054266400670555121700 : Int)/10^30,(-431475580142447467146044796 : Int)/10^30)
theorem v4219_mb_checked : Scalar.distance (sourceCoefficient 64 92 3 1) v4219_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4219_mg : Scalar.QComplex := ((-93086013795355511961642 : Int)/10^30,(277451774082385681000 : Int)/10^30)
theorem v4219_mg_checked : Scalar.distance (sourceCoefficient 64 92 3 2) v4219_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4219_upper : Scalar.QComplex := ((999992613601694455412701676394 : Int)/10^30,(-3843532496572553560162351088 : Int)/10^30)
theorem v4219_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 64 92 5) 1) 14) v4219_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4219 : Material (64 : Basis) (92 : Basis) where
  plus := ![v4219_pa,v4219_pb,v4219_pg]
  minus := ![(Primitive.Addresses.material4219 1).one,v4219_mb,v4219_mg]
  upper := v4219_upper
  lower := (Primitive.Addresses.material4219 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4219_pa_checked.trans (by decide +kernel)
    · exact v4219_pb_checked.trans (by decide +kernel)
    · exact v4219_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 64 92 Primitive.Addresses.material4219
    · exact v4219_mb_checked.trans (by decide +kernel)
    · exact v4219_mg_checked.trans (by decide +kernel)
  upper_error := v4219_upper_checked
  lower_error := reuse_lower_error 64 92 Primitive.Addresses.material4219

def v4220_pa : Scalar.QComplex := ((999997676786973847801817141433 : Int)/10^30,(-2155555764758970804776363896 : Int)/10^30)
theorem v4220_pa_checked : Scalar.distance (sourceCoefficient 64 93 1 0) v4220_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4220_pb : Scalar.QComplex := ((-930073798414254901928982 : Int)/10^30,(-431476491056444357158888581 : Int)/10^30)
theorem v4220_pb_checked : Scalar.distance (sourceCoefficient 64 93 1 1) v4220_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4220_pg : Scalar.QComplex := ((-93086210667724197350335 : Int)/10^30,(200652984184007491182 : Int)/10^30)
theorem v4220_pg_checked : Scalar.distance (sourceCoefficient 64 93 1 2) v4220_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4220_mb : Scalar.QComplex := ((-1302418230907213695978343 : Int)/10^30,(-431475527786228224429769455 : Int)/10^30)
theorem v4220_mb_checked : Scalar.distance (sourceCoefficient 64 93 3 1) v4220_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4220_mg : Scalar.QComplex := ((-93086002852985439902080 : Int)/10^30,(280982116830679652273 : Int)/10^30)
theorem v4220_mg_checked : Scalar.distance (sourceCoefficient 64 93 3 2) v4220_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4220_upper : Scalar.QComplex := ((999992467114202769833835854411 : Int)/10^30,(-3881457825365605877889635880 : Int)/10^30)
theorem v4220_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 64 93 5) 1) 14) v4220_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4220 : Material (64 : Basis) (93 : Basis) where
  plus := ![v4220_pa,v4220_pb,v4220_pg]
  minus := ![(Primitive.Addresses.material4220 1).one,v4220_mb,v4220_mg]
  upper := v4220_upper
  lower := (Primitive.Addresses.material4220 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4220_pa_checked.trans (by decide +kernel)
    · exact v4220_pb_checked.trans (by decide +kernel)
    · exact v4220_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 64 93 Primitive.Addresses.material4220
    · exact v4220_mb_checked.trans (by decide +kernel)
    · exact v4220_mg_checked.trans (by decide +kernel)
  upper_error := v4220_upper_checked
  lower_error := reuse_lower_error 64 93 Primitive.Addresses.material4220

def v4221_pa : Scalar.QComplex := ((999997579217731969437981228255 : Int)/10^30,(-2200354216001218024423681851 : Int)/10^30)
theorem v4221_pa_checked : Scalar.distance (sourceCoefficient 64 94 1 0) v4221_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4221_pb : Scalar.QComplex := ((-949403312778160261104607 : Int)/10^30,(-431476444826613284437066032 : Int)/10^30)
theorem v4221_pb_checked : Scalar.distance (sourceCoefficient 64 94 1 1) v4221_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4221_pg : Scalar.QComplex := ((-93086201139754539294554 : Int)/10^30,(204823110961551385588 : Int)/10^30)
theorem v4221_pg_checked : Scalar.distance (sourceCoefficient 64 94 1 2) v4221_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4221_mb : Scalar.QComplex := ((-1321747698179595353565472 : Int)/10^30,(-431475464875914038146447541 : Int)/10^30)
theorem v4221_mb_checked : Scalar.distance (sourceCoefficient 64 94 3 1) v4221_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4221_mg : Scalar.QComplex := ((-93085989726387736062492 : Int)/10^30,(285152233833286072113 : Int)/10^30)
theorem v4221_mg_checked : Scalar.distance (sourceCoefficient 64 94 3 2) v4221_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4221_upper : Scalar.QComplex := ((999992292227043449025605022176 : Int)/10^30,(-3926256041490162298379558282 : Int)/10^30)
theorem v4221_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 64 94 5) 1) 14) v4221_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4221 : Material (64 : Basis) (94 : Basis) where
  plus := ![v4221_pa,v4221_pb,v4221_pg]
  minus := ![(Primitive.Addresses.material4221 1).one,v4221_mb,v4221_mg]
  upper := v4221_upper
  lower := (Primitive.Addresses.material4221 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4221_pa_checked.trans (by decide +kernel)
    · exact v4221_pb_checked.trans (by decide +kernel)
    · exact v4221_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 64 94 Primitive.Addresses.material4221
    · exact v4221_mb_checked.trans (by decide +kernel)
    · exact v4221_mg_checked.trans (by decide +kernel)
  upper_error := v4221_upper_checked
  lower_error := reuse_lower_error 64 94 Primitive.Addresses.material4221

def v4222_pa : Scalar.QComplex := ((999997480818656211835986752712 : Int)/10^30,(-2244628330325910578712279453 : Int)/10^30)
theorem v4222_pa_checked : Scalar.distance (sourceCoefficient 64 95 1 0) v4222_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4222_pb : Scalar.QComplex := ((-968506586669314758498872 : Int)/10^30,(-431476398003480408105060211 : Int)/10^30)
theorem v4222_pb_checked : Scalar.distance (sourceCoefficient 64 95 1 1) v4222_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4222_pg : Scalar.QComplex := ((-93086191509162642751012 : Int)/10^30,(208944428992517103461 : Int)/10^30)
theorem v4222_pg_checked : Scalar.distance (sourceCoefficient 64 95 1 2) v4222_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4222_mb : Scalar.QComplex := ((-1340850924551473081882488 : Int)/10^30,(-431475401567533607657671836 : Int)/10^30)
theorem v4222_mb_checked : Scalar.distance (sourceCoefficient 64 95 3 1) v4222_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4222_mg : Scalar.QComplex := ((-93085976539287581978715 : Int)/10^30,(289273542018929672559 : Int)/10^30)
theorem v4222_mg_checked : Scalar.distance (sourceCoefficient 64 95 3 2) v4222_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4222_upper : Scalar.QComplex := ((999992117415009437145068179837 : Int)/10^30,(-3970529920045884305643822842 : Int)/10^30)
theorem v4222_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 64 95 5) 1) 14) v4222_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4222 : Material (64 : Basis) (95 : Basis) where
  plus := ![v4222_pa,v4222_pb,v4222_pg]
  minus := ![(Primitive.Addresses.material4222 1).one,v4222_mb,v4222_mg]
  upper := v4222_upper
  lower := (Primitive.Addresses.material4222 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4222_pa_checked.trans (by decide +kernel)
    · exact v4222_pb_checked.trans (by decide +kernel)
    · exact v4222_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 64 95 Primitive.Addresses.material4222
    · exact v4222_mb_checked.trans (by decide +kernel)
    · exact v4222_mg_checked.trans (by decide +kernel)
  upper_error := v4222_upper_checked
  lower_error := reuse_lower_error 64 95 Primitive.Addresses.material4222

def v4223_pa : Scalar.QComplex := ((999997432862582124878527686811 : Int)/10^30,(-2265892372897645085782249402 : Int)/10^30)
theorem v4223_pa_checked : Scalar.distance (sourceCoefficient 64 96 1 0) v4223_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4223_pb : Scalar.QComplex := ((-977681537299908288399379 : Int)/10^30,(-431476375114315655757479645 : Int)/10^30)
theorem v4223_pb_checked : Scalar.distance (sourceCoefficient 64 96 1 1) v4223_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4223_pg : Scalar.QComplex := ((-93086186808092645367069 : Int)/10^30,(210923822181018753281 : Int)/10^30)
theorem v4223_pg_checked : Scalar.distance (sourceCoefficient 64 96 1 2) v4223_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4223_mb : Scalar.QComplex := ((-1350025852013494884490636 : Int)/10^30,(-431475370760808208226788566 : Int)/10^30)
theorem v4223_mb_checked : Scalar.distance (sourceCoefficient 64 96 3 1) v4223_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4223_mg : Scalar.QComplex := ((-93085970130092161900919 : Int)/10^30,(291252930413601096152 : Int)/10^30)
theorem v4223_mg_checked : Scalar.distance (sourceCoefficient 64 96 3 2) v4223_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4223_upper : Scalar.QComplex := ((999992032759198355186013052218 : Int)/10^30,(-3991793848179491918988138891 : Int)/10^30)
theorem v4223_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 64 96 5) 1) 14) v4223_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4223 : Material (64 : Basis) (96 : Basis) where
  plus := ![v4223_pa,v4223_pb,v4223_pg]
  minus := ![(Primitive.Addresses.material4223 1).one,v4223_mb,v4223_mg]
  upper := v4223_upper
  lower := (Primitive.Addresses.material4223 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4223_pa_checked.trans (by decide +kernel)
    · exact v4223_pb_checked.trans (by decide +kernel)
    · exact v4223_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 64 96 Primitive.Addresses.material4223
    · exact v4223_mb_checked.trans (by decide +kernel)
    · exact v4223_mg_checked.trans (by decide +kernel)
  upper_error := v4223_upper_checked
  lower_error := reuse_lower_error 64 96 Primitive.Addresses.material4223

def v4224_pa : Scalar.QComplex := ((999997264408509919634334261818 : Int)/10^30,(-2339054402253169213654079587 : Int)/10^30)
theorem v4224_pa_checked : Scalar.distance (sourceCoefficient 64 97 1 0) v4224_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4224_pb : Scalar.QComplex := ((-1009249286716193840562458 : Int)/10^30,(-431476294373591579212279181 : Int)/10^30)
theorem v4224_pb_checked : Scalar.distance (sourceCoefficient 64 97 1 1) v4224_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4224_pg : Scalar.QComplex := ((-93086170258246272387153 : Int)/10^30,(217734211963296318902 : Int)/10^30)
theorem v4224_pg_checked : Scalar.distance (sourceCoefficient 64 97 1 2) v4224_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4224_mb : Scalar.QComplex := ((-1381593520000056160713969 : Int)/10^30,(-431475262778568207544311013 : Int)/10^30)
theorem v4224_mb_checked : Scalar.distance (sourceCoefficient 64 97 3 1) v4224_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4224_mg : Scalar.QComplex := ((-93085947703192297649127 : Int)/10^30,(298063303378287253171 : Int)/10^30)
theorem v4224_mg_checked : Scalar.distance (sourceCoefficient 64 97 3 2) v4224_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4224_upper : Scalar.QComplex := ((999991738034351582315833061613 : Int)/10^30,(-4064955477832320945287887708 : Int)/10^30)
theorem v4224_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 64 97 5) 1) 14) v4224_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4224 : Material (64 : Basis) (97 : Basis) where
  plus := ![v4224_pa,v4224_pb,v4224_pg]
  minus := ![(Primitive.Addresses.material4224 1).one,v4224_mb,v4224_mg]
  upper := v4224_upper
  lower := (Primitive.Addresses.material4224 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4224_pa_checked.trans (by decide +kernel)
    · exact v4224_pb_checked.trans (by decide +kernel)
    · exact v4224_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 64 97 Primitive.Addresses.material4224
    · exact v4224_mb_checked.trans (by decide +kernel)
    · exact v4224_mg_checked.trans (by decide +kernel)
  upper_error := v4224_upper_checked
  lower_error := reuse_lower_error 64 97 Primitive.Addresses.material4224

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
