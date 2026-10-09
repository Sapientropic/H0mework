import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B019
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B020

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v465_pa : Scalar.QComplex := ((999996042562311143799058447291 : Int)/10^30,(2813336047542017456029585584 : Int)/10^30)
theorem v465_pa_checked : Scalar.distance (sourceCoefficient 4 88 1 0) v465_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v465_pb : Scalar.QComplex := ((1213885507888618725464557 : Int)/10^30,(-431473767619376590181313853 : Int)/10^30)
theorem v465_pb_checked : Scalar.distance (sourceCoefficient 4 88 1 1) v465_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v465_pg : Scalar.QComplex := ((-93085840830069532241083 : Int)/10^30,(-261882787907808096304 : Int)/10^30)
theorem v465_pg_checked : Scalar.distance (sourceCoefficient 4 88 1 2) v465_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v465_mb : Scalar.QComplex := ((841542627305156844747795 : Int)/10^30,(-431474654490495514252216352 : Int)/10^30)
theorem v465_mb_checked : Scalar.distance (sourceCoefficient 4 88 3 1) v465_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v465_mg : Scalar.QComplex := ((-93086032163007959630083 : Int)/10^30,(-181553802191168162716 : Int)/10^30)
theorem v465_mg_checked : Scalar.distance (sourceCoefficient 4 88 3 2) v465_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v465_upper : Scalar.QComplex := ((999999408748467739046387388017 : Int)/10^30,(1087429406878227118463270670 : Int)/10^30)
theorem v465_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 88 5) 1) 14) v465_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material465 : Material (4 : Basis) (88 : Basis) where
  plus := ![v465_pa,v465_pb,v465_pg]
  minus := ![(Primitive.Addresses.material465 1).one,v465_mb,v465_mg]
  upper := v465_upper
  lower := (Primitive.Addresses.material465 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v465_pa_checked.trans (by decide +kernel)
    · exact v465_pb_checked.trans (by decide +kernel)
    · exact v465_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 88 Primitive.Addresses.material465
    · exact v465_mb_checked.trans (by decide +kernel)
    · exact v465_mg_checked.trans (by decide +kernel)
  upper_error := v465_upper_checked
  lower_error := reuse_lower_error 4 88 Primitive.Addresses.material465

def v466_pa : Scalar.QComplex := ((999996087698002705185673516813 : Int)/10^30,(2797246626324305823269913063 : Int)/10^30)
theorem v466_pa_checked : Scalar.distance (sourceCoefficient 4 89 1 0) v466_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v466_pb : Scalar.QComplex := ((1206943282646001709787491 : Int)/10^30,(-431473774733031686045266920 : Int)/10^30)
theorem v466_pb_checked : Scalar.distance (sourceCoefficient 4 89 1 1) v466_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v466_pg : Scalar.QComplex := ((-93085843698174072770905 : Int)/10^30,(-260385080948341328562 : Int)/10^30)
theorem v466_pg_checked : Scalar.distance (sourceCoefficient 4 89 1 2) v466_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v466_mb : Scalar.QComplex := ((834600398508683601665950 : Int)/10^30,(-431474655613320243216994472 : Int)/10^30)
theorem v466_mb_checked : Scalar.distance (sourceCoefficient 4 89 3 1) v466_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v466_mg : Scalar.QComplex := ((-93086033738657780431122 : Int)/10^30,(-180056093314321100729 : Int)/10^30)
theorem v466_mg_checked : Scalar.distance (sourceCoefficient 4 89 3 2) v466_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v466_upper : Scalar.QComplex := ((999999426115210675243092524763 : Int)/10^30,(1071339931723709436303134756 : Int)/10^30)
theorem v466_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 89 5) 1) 14) v466_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material466 : Material (4 : Basis) (89 : Basis) where
  plus := ![v466_pa,v466_pb,v466_pg]
  minus := ![(Primitive.Addresses.material466 1).one,v466_mb,v466_mg]
  upper := v466_upper
  lower := (Primitive.Addresses.material466 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v466_pa_checked.trans (by decide +kernel)
    · exact v466_pb_checked.trans (by decide +kernel)
    · exact v466_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 89 Primitive.Addresses.material466
    · exact v466_mb_checked.trans (by decide +kernel)
    · exact v466_mg_checked.trans (by decide +kernel)
  upper_error := v466_upper_checked
  lower_error := reuse_lower_error 4 89 Primitive.Addresses.material466

def v467_pa : Scalar.QComplex := ((999996160650797181800298170523 : Int)/10^30,(2771043786199362498791215269 : Int)/10^30)
theorem v467_pa_checked : Scalar.distance (sourceCoefficient 4 90 1 0) v467_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v467_pb : Scalar.QComplex := ((1195637344070795399900775 : Int)/10^30,(-431473785999385824891892347 : Int)/10^30)
theorem v467_pb_checked : Scalar.distance (sourceCoefficient 4 90 1 1) v467_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v467_pg : Scalar.QComplex := ((-93085848308924292539445 : Int)/10^30,(-257945951884125833007 : Int)/10^30)
theorem v467_pg_checked : Scalar.distance (sourceCoefficient 4 90 1 2) v467_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v467_mb : Scalar.QComplex := ((823294454420838726176812 : Int)/10^30,(-431474657123154397253044335 : Int)/10^30)
theorem v467_mb_checked : Scalar.distance (sourceCoefficient 4 90 3 1) v467_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v467_mg : Scalar.QComplex := ((-93086036244547755283729 : Int)/10^30,(-177616961179435050308 : Int)/10^30)
theorem v467_mg_checked : Scalar.distance (sourceCoefficient 4 90 3 2) v467_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v467_upper : Scalar.QComplex := ((999999453844171544675028007083 : Int)/10^30,(1045137004714913435287941387 : Int)/10^30)
theorem v467_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 90 5) 1) 14) v467_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material467 : Material (4 : Basis) (90 : Basis) where
  plus := ![v467_pa,v467_pb,v467_pg]
  minus := ![(Primitive.Addresses.material467 1).one,v467_mb,v467_mg]
  upper := v467_upper
  lower := (Primitive.Addresses.material467 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v467_pa_checked.trans (by decide +kernel)
    · exact v467_pb_checked.trans (by decide +kernel)
    · exact v467_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 90 Primitive.Addresses.material467
    · exact v467_mb_checked.trans (by decide +kernel)
    · exact v467_mg_checked.trans (by decide +kernel)
  upper_error := v467_upper_checked
  lower_error := reuse_lower_error 4 90 Primitive.Addresses.material467

def v468_pa : Scalar.QComplex := ((999996201445427028833450627466 : Int)/10^30,(2756282771583040835116781648 : Int)/10^30)
theorem v468_pa_checked : Scalar.distance (sourceCoefficient 4 91 1 0) v468_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v468_pb : Scalar.QComplex := ((1189268297254361339648978 : Int)/10^30,(-431473792172198530331049303 : Int)/10^30)
theorem v468_pb_checked : Scalar.distance (sourceCoefficient 4 91 1 1) v468_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v468_pg : Scalar.QComplex := ((-93085850873493850665824 : Int)/10^30,(-256571901643129535814 : Int)/10^30)
theorem v468_pg_checked : Scalar.distance (sourceCoefficient 4 91 1 2) v468_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v468_mb : Scalar.QComplex := ((816925404649032523872488 : Int)/10^30,(-431474657799764252909519945 : Int)/10^30)
theorem v468_mb_checked : Scalar.distance (sourceCoefficient 4 91 3 1) v468_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v468_mg : Scalar.QComplex := ((-93086037623372885449429 : Int)/10^30,(-176242909236952430297 : Int)/10^30)
theorem v468_mg_checked : Scalar.distance (sourceCoefficient 4 91 3 2) v468_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v468_upper : Scalar.QComplex := ((999999469162568513913354579948 : Int)/10^30,(1030375941675558835975378341 : Int)/10^30)
theorem v468_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 91 5) 1) 14) v468_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material468 : Material (4 : Basis) (91 : Basis) where
  plus := ![v468_pa,v468_pb,v468_pg]
  minus := ![(Primitive.Addresses.material468 1).one,v468_mb,v468_mg]
  upper := v468_upper
  lower := (Primitive.Addresses.material468 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v468_pa_checked.trans (by decide +kernel)
    · exact v468_pb_checked.trans (by decide +kernel)
    · exact v468_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 91 Primitive.Addresses.material468
    · exact v468_mb_checked.trans (by decide +kernel)
    · exact v468_mg_checked.trans (by decide +kernel)
  upper_error := v468_upper_checked
  lower_error := reuse_lower_error 4 91 Primitive.Addresses.material468

def v469_pa : Scalar.QComplex := ((999996289014893304404829702661 : Int)/10^30,(2724326786929337562078563972 : Int)/10^30)
theorem v469_pa_checked : Scalar.distance (sourceCoefficient 4 92 1 0) v469_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v469_pb : Scalar.QComplex := ((1175480007298028670586154 : Int)/10^30,(-431473805106229115582338205 : Int)/10^30)
theorem v469_pb_checked : Scalar.distance (sourceCoefficient 4 92 1 1) v469_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v469_pg : Scalar.QComplex := ((-93085856344441683618158 : Int)/10^30,(-253597233018973536318 : Int)/10^30)
theorem v469_pg_checked : Scalar.distance (sourceCoefficient 4 92 1 2) v469_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v469_mb : Scalar.QComplex := ((803137108665224493574933 : Int)/10^30,(-431474658835116791441987099 : Int)/10^30)
theorem v469_mb_checked : Scalar.distance (sourceCoefficient 4 92 3 1) v469_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v469_mg : Scalar.QComplex := ((-93086040527313632772702 : Int)/10^30,(-173268236999219931153 : Int)/10^30)
theorem v469_mg_checked : Scalar.distance (sourceCoefficient 4 92 3 2) v469_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v469_upper : Scalar.QComplex := ((999999501578773877041348076434 : Int)/10^30,(998419853479586339267058023 : Int)/10^30)
theorem v469_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 92 5) 1) 14) v469_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material469 : Material (4 : Basis) (92 : Basis) where
  plus := ![v469_pa,v469_pb,v469_pg]
  minus := ![(Primitive.Addresses.material469 1).one,v469_mb,v469_mg]
  upper := v469_upper
  lower := (Primitive.Addresses.material469 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v469_pa_checked.trans (by decide +kernel)
    · exact v469_pb_checked.trans (by decide +kernel)
    · exact v469_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 92 Primitive.Addresses.material469
    · exact v469_mb_checked.trans (by decide +kernel)
    · exact v469_mg_checked.trans (by decide +kernel)
  upper_error := v469_upper_checked
  lower_error := reuse_lower_error 4 92 Primitive.Addresses.material469

def v470_pa : Scalar.QComplex := ((999996391617479802139576475228 : Int)/10^30,(2686401314020544618745398341 : Int)/10^30)
theorem v470_pa_checked : Scalar.distance (sourceCoefficient 4 93 1 0) v470_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v470_pb : Scalar.QComplex := ((1159116018725449701710998 : Int)/10^30,(-431473819694016270250452514 : Int)/10^30)
theorem v470_pb_checked : Scalar.distance (sourceCoefficient 4 93 1 1) v470_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v470_pg : Scalar.QComplex := ((-93085862693468423351187 : Int)/10^30,(-250066886193450586023 : Int)/10^30)
theorem v470_pg_checked : Scalar.distance (sourceCoefficient 4 93 1 2) v470_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v470_mb : Scalar.QComplex := ((786773113597103036559806 : Int)/10^30,(-431474659301513382960933517 : Int)/10^30)
theorem v470_mb_checked : Scalar.distance (sourceCoefficient 4 93 3 1) v470_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v470_mg : Scalar.QComplex := ((-93086043829807698965236 : Int)/10^30,(-169737886009282321980 : Int)/10^30)
theorem v470_mg_checked : Scalar.distance (sourceCoefficient 4 93 3 2) v470_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v470_upper : Scalar.QComplex := ((999999538725281891725444690566 : Int)/10^30,(960494259973573993430224516 : Int)/10^30)
theorem v470_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 93 5) 1) 14) v470_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material470 : Material (4 : Basis) (93 : Basis) where
  plus := ![v470_pa,v470_pb,v470_pg]
  minus := ![(Primitive.Addresses.material470 1).one,v470_mb,v470_mg]
  upper := v470_upper
  lower := (Primitive.Addresses.material470 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v470_pa_checked.trans (by decide +kernel)
    · exact v470_pb_checked.trans (by decide +kernel)
    · exact v470_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 93 Primitive.Addresses.material470
    · exact v470_mb_checked.trans (by decide +kernel)
    · exact v470_mg_checked.trans (by decide +kernel)
  upper_error := v470_upper_checked
  lower_error := reuse_lower_error 4 93 Primitive.Addresses.material470

def v471_pa : Scalar.QComplex := ((999996510960931731709312879708 : Int)/10^30,(2641602915493348987414936267 : Int)/10^30)
theorem v471_pa_checked : Scalar.distance (sourceCoefficient 4 94 1 0) v471_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v471_pb : Scalar.QComplex := ((1139786519525025603902484 : Int)/10^30,(-431473835859415045933184314 : Int)/10^30)
theorem v471_pb_checked : Scalar.distance (sourceCoefficient 4 94 1 1) v471_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v471_pg : Scalar.QComplex := ((-93085869991844204170989 : Int)/10^30,(-245896763505105125707 : Int)/10^30)
theorem v471_pg_checked : Scalar.distance (sourceCoefficient 4 94 1 2) v471_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v471_mb : Scalar.QComplex := ((767443607643923811943282 : Int)/10^30,(-431474658786418897887881230 : Int)/10^30)
theorem v471_mb_checked : Scalar.distance (sourceCoefficient 4 94 3 1) v471_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v471_mg : Scalar.QComplex := ((-93086047529552697577899 : Int)/10^30,(-165567758575494530353 : Int)/10^30)
theorem v471_mg_checked : Scalar.distance (sourceCoefficient 4 94 3 2) v471_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v471_upper : Scalar.QComplex := ((999999580750584294270483482782 : Int)/10^30,(915695722192359301751676086 : Int)/10^30)
theorem v471_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 94 5) 1) 14) v471_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material471 : Material (4 : Basis) (94 : Basis) where
  plus := ![v471_pa,v471_pb,v471_pg]
  minus := ![(Primitive.Addresses.material471 1).one,v471_mb,v471_mg]
  upper := v471_upper
  lower := (Primitive.Addresses.material471 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v471_pa_checked.trans (by decide +kernel)
    · exact v471_pb_checked.trans (by decide +kernel)
    · exact v471_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 94 Primitive.Addresses.material471
    · exact v471_mb_checked.trans (by decide +kernel)
    · exact v471_mg_checked.trans (by decide +kernel)
  upper_error := v471_upper_checked
  lower_error := reuse_lower_error 4 94 Primitive.Addresses.material471

def v472_pa : Scalar.QComplex := ((999996626935750010721673690723 : Int)/10^30,(2597328843719278087839815526 : Int)/10^30)
theorem v472_pa_checked : Scalar.distance (sourceCoefficient 4 95 1 0) v472_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v472_pb : Scalar.QComplex := ((1120683257873539809676453 : Int)/10^30,(-431473850701221134762042869 : Int)/10^30)
theorem v472_pb_checked : Scalar.distance (sourceCoefficient 4 95 1 1) v472_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v472_pg : Scalar.QComplex := ((-93085876990657767280271 : Int)/10^30,(-241775448774862879710 : Int)/10^30)
theorem v472_pg_checked : Scalar.distance (sourceCoefficient 4 95 1 2) v472_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v472_mb : Scalar.QComplex := ((748340340297645188225933 : Int)/10^30,(-431474657142965034167802857 : Int)/10^30)
theorem v472_mb_checked : Scalar.distance (sourceCoefficient 4 95 3 1) v472_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v472_mg : Scalar.QComplex := ((-93086050971854659634990 : Int)/10^30,(-161446439340145221711 : Int)/10^30)
theorem v472_mg_checked : Scalar.distance (sourceCoefficient 4 95 3 2) v472_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v472_upper : Scalar.QComplex := ((999999620312198472784074724246 : Int)/10^30,(871421516197302315600655670 : Int)/10^30)
theorem v472_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 95 5) 1) 14) v472_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material472 : Material (4 : Basis) (95 : Basis) where
  plus := ![v472_pa,v472_pb,v472_pg]
  minus := ![(Primitive.Addresses.material472 1).one,v472_mb,v472_mg]
  upper := v472_upper
  lower := (Primitive.Addresses.material472 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v472_pa_checked.trans (by decide +kernel)
    · exact v472_pb_checked.trans (by decide +kernel)
    · exact v472_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 95 Primitive.Addresses.material472
    · exact v472_mb_checked.trans (by decide +kernel)
    · exact v472_mg_checked.trans (by decide +kernel)
  upper_error := v472_upper_checked
  lower_error := reuse_lower_error 4 95 Primitive.Addresses.material472

def v473_pa : Scalar.QComplex := ((999996681939521427880887106388 : Int)/10^30,(2576064818209918172855354068 : Int)/10^30)
theorem v473_pa_checked : Scalar.distance (sourceCoefficient 4 96 1 0) v473_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v473_pb : Scalar.QComplex := ((1111508312150924850615011 : Int)/10^30,(-431473857428593822922463866 : Int)/10^30)
theorem v473_pb_checked : Scalar.distance (sourceCoefficient 4 96 1 1) v473_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v473_pg : Scalar.QComplex := ((-93085880276385806251894 : Int)/10^30,(-239796056909917359814 : Int)/10^30)
theorem v473_pg_checked : Scalar.distance (sourceCoefficient 4 96 1 2) v473_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v473_mb : Scalar.QComplex := ((739165392185862197164109 : Int)/10^30,(-431474655952770283018948907 : Int)/10^30)
theorem v473_mb_checked : Scalar.distance (sourceCoefficient 4 96 3 1) v473_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v473_mg : Scalar.QComplex := ((-93086052549455444232164 : Int)/10^30,(-159467045376782441877 : Int)/10^30)
theorem v473_mg_checked : Scalar.distance (sourceCoefficient 4 96 3 2) v473_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v473_upper : Scalar.QComplex := ((999999638616108996456986150545 : Int)/10^30,(850157427426690986054391147 : Int)/10^30)
theorem v473_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 96 5) 1) 14) v473_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material473 : Material (4 : Basis) (96 : Basis) where
  plus := ![v473_pa,v473_pb,v473_pg]
  minus := ![(Primitive.Addresses.material473 1).one,v473_mb,v473_mg]
  upper := v473_upper
  lower := (Primitive.Addresses.material473 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v473_pa_checked.trans (by decide +kernel)
    · exact v473_pb_checked.trans (by decide +kernel)
    · exact v473_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 96 Primitive.Addresses.material473
    · exact v473_mb_checked.trans (by decide +kernel)
    · exact v473_mg_checked.trans (by decide +kernel)
  upper_error := v473_upper_checked
  lower_error := reuse_lower_error 4 96 Primitive.Addresses.material473

def v474_pa : Scalar.QComplex := ((999996867733804153821234492227 : Int)/10^30,(2502902830834796089472309273 : Int)/10^30)
theorem v474_pa_checked : Scalar.distance (sourceCoefficient 4 97 1 0) v474_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v474_pb : Scalar.QComplex := ((1079940574810230952244051 : Int)/10^30,(-431473878587880395225612603 : Int)/10^30)
theorem v474_pb_checked : Scalar.distance (sourceCoefficient 4 97 1 1) v474_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v474_pg : Scalar.QComplex := ((-93085891206281666003060 : Int)/10^30,(-232985670384121694325 : Int)/10^30)
theorem v474_pg_checked : Scalar.distance (sourceCoefficient 4 97 1 2) v474_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v474_mb : Scalar.QComplex := ((707597648339768294594977 : Int)/10^30,(-431474649870513409845528202 : Int)/10^30)
theorem v474_mb_checked : Scalar.distance (sourceCoefficient 4 97 3 1) v474_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v474_mg : Scalar.QComplex := ((-93086057602290390944749 : Int)/10^30,(-152656651954797067252 : Int)/10^30)
theorem v474_mg_checked : Scalar.distance (sourceCoefficient 4 97 3 2) v474_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v474_upper : Scalar.QComplex := ((999999698139161997825108354870 : Int)/10^30,(776995228353678027859071561 : Int)/10^30)
theorem v474_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 4 97 5) 1) 14) v474_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material474 : Material (4 : Basis) (97 : Basis) where
  plus := ![v474_pa,v474_pb,v474_pg]
  minus := ![(Primitive.Addresses.material474 1).one,v474_mb,v474_mg]
  upper := v474_upper
  lower := (Primitive.Addresses.material474 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v474_pa_checked.trans (by decide +kernel)
    · exact v474_pb_checked.trans (by decide +kernel)
    · exact v474_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 4 97 Primitive.Addresses.material474
    · exact v474_mb_checked.trans (by decide +kernel)
    · exact v474_mg_checked.trans (by decide +kernel)
  upper_error := v474_upper_checked
  lower_error := reuse_lower_error 4 97 Primitive.Addresses.material474

def v475_pa : Scalar.QComplex := ((999990914193895489621603340126 : Int)/10^30,(4262807719936261450147998357 : Int)/10^30)
theorem v475_pa_checked : Scalar.distance (sourceCoefficient 5 6 1 0) v475_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v475_pb : Scalar.QComplex := ((1839301200024708861879959 : Int)/10^30,(-431472543293165256425428107 : Int)/10^30)
theorem v475_pb_checked : Scalar.distance (sourceCoefficient 5 6 1 1) v475_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v475_pg : Scalar.QComplex := ((-93085470072075932240821 : Int)/10^30,(-396809065767373181767 : Int)/10^30)
theorem v475_pg_checked : Scalar.distance (sourceCoefficient 5 6 1 2) v475_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v475_mb : Scalar.QComplex := ((1466959143108780665167334 : Int)/10^30,(-431473969870314689404586332 : Int)/10^30)
theorem v475_mb_checked : Scalar.distance (sourceCoefficient 5 6 3 1) v475_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v475_mg : Scalar.QComplex := ((-93085777840453348608613 : Int)/10^30,(-316480349758963722176 : Int)/10^30)
theorem v475_mg_checked : Scalar.distance (sourceCoefficient 5 6 3 2) v475_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v475_upper : Scalar.QComplex := ((999996782044301696732010654778 : Int)/10^30,(2536907771553325455305084234 : Int)/10^30)
theorem v475_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 6 5) 1) 14) v475_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material475 : Material (5 : Basis) (6 : Basis) where
  plus := ![v475_pa,v475_pb,v475_pg]
  minus := ![(Primitive.Addresses.material475 1).one,v475_mb,v475_mg]
  upper := v475_upper
  lower := (Primitive.Addresses.material475 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v475_pa_checked.trans (by decide +kernel)
    · exact v475_pb_checked.trans (by decide +kernel)
    · exact v475_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 6 Primitive.Addresses.material475
    · exact v475_mb_checked.trans (by decide +kernel)
    · exact v475_mg_checked.trans (by decide +kernel)
  upper_error := v475_upper_checked
  lower_error := reuse_lower_error 5 6 Primitive.Addresses.material475

def v476_pa : Scalar.QComplex := ((999991165884872801502415763166 : Int)/10^30,(4203350117799719354130947349 : Int)/10^30)
theorem v476_pa_checked : Scalar.distance (sourceCoefficient 5 7 1 0) v476_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v476_pb : Scalar.QComplex := ((1813646505217071287806488 : Int)/10^30,(-431472618846322754445721687 : Int)/10^30)
theorem v476_pb_checked : Scalar.distance (sourceCoefficient 5 7 1 1) v476_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v476_pg : Scalar.QComplex := ((-93085489936454103197211 : Int)/10^30,(-391274361652596105265 : Int)/10^30)
theorem v476_pg_checked : Scalar.distance (sourceCoefficient 5 7 1 2) v476_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v476_mb : Scalar.QComplex := ((1441304392654586312556377 : Int)/10^30,(-431474023284597881102184790 : Int)/10^30)
theorem v476_mb_checked : Scalar.distance (sourceCoefficient 5 7 3 1) v476_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v476_mg : Scalar.QComplex := ((-93085792928623745916396 : Int)/10^30,(-310945630562946232926 : Int)/10^30)
theorem v476_mg_checked : Scalar.distance (sourceCoefficient 5 7 3 2) v476_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v476_upper : Scalar.QComplex := ((999996931116476808326748434058 : Int)/10^30,(2477449823576103747886621018 : Int)/10^30)
theorem v476_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 7 5) 1) 14) v476_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material476 : Material (5 : Basis) (7 : Basis) where
  plus := ![v476_pa,v476_pb,v476_pg]
  minus := ![(Primitive.Addresses.material476 1).one,v476_mb,v476_mg]
  upper := v476_upper
  lower := (Primitive.Addresses.material476 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v476_pa_checked.trans (by decide +kernel)
    · exact v476_pb_checked.trans (by decide +kernel)
    · exact v476_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 7 Primitive.Addresses.material476
    · exact v476_mb_checked.trans (by decide +kernel)
    · exact v476_mg_checked.trans (by decide +kernel)
  upper_error := v476_upper_checked
  lower_error := reuse_lower_error 5 7 Primitive.Addresses.material476

def v477_pa : Scalar.QComplex := ((999991326273191821701231382394 : Int)/10^30,(4165018413263001965421030069 : Int)/10^30)
theorem v477_pa_checked : Scalar.distance (sourceCoefficient 5 8 1 0) v477_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v477_pb : Scalar.QComplex := ((1797107188310683437347642 : Int)/10^30,(-431472666476398806196042363 : Int)/10^30)
theorem v477_pb_checked : Scalar.distance (sourceCoefficient 5 8 1 1) v477_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v477_pg : Scalar.QComplex := ((-93085502539267968459389 : Int)/10^30,(-387706194941507775252 : Int)/10^30)
theorem v477_pg_checked : Scalar.distance (sourceCoefficient 5 8 1 2) v477_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v477_mb : Scalar.QComplex := ((1424765040803931576801840 : Int)/10^30,(-431474056641970610967032260 : Int)/10^30)
theorem v477_mb_checked : Scalar.distance (sourceCoefficient 5 8 3 1) v477_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v477_mg : Scalar.QComplex := ((-93085802452265751168811 : Int)/10^30,(-307377454304788686670 : Int)/10^30)
theorem v477_mg_checked : Scalar.distance (sourceCoefficient 5 8 3 2) v477_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v477_upper : Scalar.QComplex := ((999997025347512343662123050035 : Int)/10^30,(2439117899314269194078387452 : Int)/10^30)
theorem v477_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 8 5) 1) 14) v477_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material477 : Material (5 : Basis) (8 : Basis) where
  plus := ![v477_pa,v477_pb,v477_pg]
  minus := ![(Primitive.Addresses.material477 1).one,v477_mb,v477_mg]
  upper := v477_upper
  lower := (Primitive.Addresses.material477 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v477_pa_checked.trans (by decide +kernel)
    · exact v477_pb_checked.trans (by decide +kernel)
    · exact v477_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 8 Primitive.Addresses.material477
    · exact v477_mb_checked.trans (by decide +kernel)
    · exact v477_mg_checked.trans (by decide +kernel)
  upper_error := v477_upper_checked
  lower_error := reuse_lower_error 5 8 Primitive.Addresses.material477

def v478_pa : Scalar.QComplex := ((999991414176888855526612515052 : Int)/10^30,(4143859614650386646518121405 : Int)/10^30)
theorem v478_pa_checked : Scalar.distance (sourceCoefficient 5 9 1 0) v478_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v478_pb : Scalar.QComplex := ((1787977616144137180668112 : Int)/10^30,(-431472692405736070347315764 : Int)/10^30)
theorem v478_pb_checked : Scalar.distance (sourceCoefficient 5 9 1 1) v478_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v478_pg : Scalar.QComplex := ((-93085509427569646723053 : Int)/10^30,(-385736595092236646647 : Int)/10^30)
theorem v478_pg_checked : Scalar.distance (sourceCoefficient 5 9 1 2) v478_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v478_mb : Scalar.QComplex := ((1415635449660892034824203 : Int)/10^30,(-431474074692888621378230867 : Int)/10^30)
theorem v478_mb_checked : Scalar.distance (sourceCoefficient 5 9 3 1) v478_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v478_mg : Scalar.QComplex := ((-93085807640888902166200 : Int)/10^30,(-305407849244595486358 : Int)/10^30)
theorem v478_mg_checked : Scalar.distance (sourceCoefficient 5 9 3 2) v478_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v478_upper : Scalar.QComplex := ((999997076732911561098363194293 : Int)/10^30,(2417958980501392402303461850 : Int)/10^30)
theorem v478_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 9 5) 1) 14) v478_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material478 : Material (5 : Basis) (9 : Basis) where
  plus := ![v478_pa,v478_pb,v478_pg]
  minus := ![(Primitive.Addresses.material478 1).one,v478_mb,v478_mg]
  upper := v478_upper
  lower := (Primitive.Addresses.material478 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v478_pa_checked.trans (by decide +kernel)
    · exact v478_pb_checked.trans (by decide +kernel)
    · exact v478_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 9 Primitive.Addresses.material478
    · exact v478_mb_checked.trans (by decide +kernel)
    · exact v478_mg_checked.trans (by decide +kernel)
  upper_error := v478_upper_checked
  lower_error := reuse_lower_error 5 9 Primitive.Addresses.material478

def v479_pa : Scalar.QComplex := ((999991586824305828707350729969 : Int)/10^30,(4101984959360202761874434006 : Int)/10^30)
theorem v479_pa_checked : Scalar.distance (sourceCoefficient 5 10 1 0) v479_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v479_pb : Scalar.QComplex := ((1769909592565719569378010 : Int)/10^30,(-431472742962326605927947404 : Int)/10^30)
theorem v479_pb_checked : Scalar.distance (sourceCoefficient 5 10 1 1) v479_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v479_pg : Scalar.QComplex := ((-93085522916642492108747 : Int)/10^30,(-381838627413706228577 : Int)/10^30)
theorem v479_pg_checked : Scalar.distance (sourceCoefficient 5 10 1 2) v479_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v479_mb : Scalar.QComplex := ((1397567389181964703355369 : Int)/10^30,(-431474109657569737829276561 : Int)/10^30)
theorem v479_mb_checked : Scalar.distance (sourceCoefficient 5 10 3 1) v479_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v479_mg : Scalar.QComplex := ((-93085817766186176329065 : Int)/10^30,(-301509871376994240649 : Int)/10^30)
theorem v479_mg_checked : Scalar.distance (sourceCoefficient 5 10 3 2) v479_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v479_upper : Scalar.QComplex := ((999997177108215204427748503615 : Int)/10^30,(2376084089604809385450915149 : Int)/10^30)
theorem v479_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 10 5) 1) 14) v479_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material479 : Material (5 : Basis) (10 : Basis) where
  plus := ![v479_pa,v479_pb,v479_pg]
  minus := ![(Primitive.Addresses.material479 1).one,v479_mb,v479_mg]
  upper := v479_upper
  lower := (Primitive.Addresses.material479 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v479_pa_checked.trans (by decide +kernel)
    · exact v479_pb_checked.trans (by decide +kernel)
    · exact v479_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 10 Primitive.Addresses.material479
    · exact v479_mb_checked.trans (by decide +kernel)
    · exact v479_mg_checked.trans (by decide +kernel)
  upper_error := v479_upper_checked
  lower_error := reuse_lower_error 5 10 Primitive.Addresses.material479

def v480_pa : Scalar.QComplex := ((999991623754898717726971031280 : Int)/10^30,(4092972030332304787647261365 : Int)/10^30)
theorem v480_pa_checked : Scalar.distance (sourceCoefficient 5 11 1 0) v480_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v480_pb : Scalar.QComplex := ((1766020705415902398614532 : Int)/10^30,(-431472753711986503313594170 : Int)/10^30)
theorem v480_pb_checked : Scalar.distance (sourceCoefficient 5 11 1 1) v480_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v480_pg : Scalar.QComplex := ((-93085525795069927043176 : Int)/10^30,(-380999644854406291171 : Int)/10^30)
theorem v480_pg_checked : Scalar.distance (sourceCoefficient 5 11 1 2) v480_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v480_mb : Scalar.QComplex := ((1393678494203685604657250 : Int)/10^30,(-431474117051291171308433611 : Int)/10^30)
theorem v480_mb_checked : Scalar.distance (sourceCoefficient 5 11 3 1) v480_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v480_mg : Scalar.QComplex := ((-93085819920608377189339 : Int)/10^30,(-300670886646132616678 : Int)/10^30)
theorem v480_mg_checked : Scalar.distance (sourceCoefficient 5 11 3 2) v480_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v480_upper : Scalar.QComplex := ((999997198483255234049835967042 : Int)/10^30,(2367071110261757456030005603 : Int)/10^30)
theorem v480_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 11 5) 1) 14) v480_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material480 : Material (5 : Basis) (11 : Basis) where
  plus := ![v480_pa,v480_pb,v480_pg]
  minus := ![(Primitive.Addresses.material480 1).one,v480_mb,v480_mg]
  upper := v480_upper
  lower := (Primitive.Addresses.material480 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v480_pa_checked.trans (by decide +kernel)
    · exact v480_pb_checked.trans (by decide +kernel)
    · exact v480_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 11 Primitive.Addresses.material480
    · exact v480_mb_checked.trans (by decide +kernel)
    · exact v480_mg_checked.trans (by decide +kernel)
  upper_error := v480_upper_checked
  lower_error := reuse_lower_error 5 11 Primitive.Addresses.material480

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
