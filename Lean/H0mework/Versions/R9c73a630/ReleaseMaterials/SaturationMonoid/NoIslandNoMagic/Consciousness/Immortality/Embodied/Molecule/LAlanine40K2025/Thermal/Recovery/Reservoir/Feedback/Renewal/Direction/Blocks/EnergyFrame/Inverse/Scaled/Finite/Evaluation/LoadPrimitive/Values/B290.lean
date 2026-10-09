import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B193
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B194

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4641_pa : Scalar.QComplex := ((999997066003444260562174288754 : Int)/10^30,(-2422392309916601134795429685 : Int)/10^30)
theorem v4641_pa_checked : Scalar.distance (sourceCoefficient 82 91 1 0) v4641_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4641_pb : Scalar.QComplex := ((-1045207820935100157955194 : Int)/10^30,(-431476251811143725192895879 : Int)/10^30)
theorem v4641_pb_checked : Scalar.distance (sourceCoefficient 82 91 1 1) v4641_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4641_pg : Scalar.QComplex := ((-93086156432651578980722 : Int)/10^30,(225491851094463396485 : Int)/10^30)
theorem v4641_pg_checked : Scalar.distance (sourceCoefficient 82 91 1 2) v4641_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4641_mb : Scalar.QComplex := ((-1417552004100481245681558 : Int)/10^30,(-431475189185540682815410262 : Int)/10^30)
theorem v4641_mb_checked : Scalar.distance (sourceCoefficient 82 91 3 1) v4641_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4641_mg : Scalar.QComplex := ((-93085927183109573042734 : Int)/10^30,(305820927690065201859 : Int)/10^30)
theorem v4641_mg_checked : Scalar.distance (sourceCoefficient 82 91 3 2) v4641_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4641_upper : Scalar.QComplex := ((999991395795913153124147276544 : Int)/10^30,(-4148292918944584799456769104 : Int)/10^30)
theorem v4641_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 82 91 5) 1) 14) v4641_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4641 : Material (82 : Basis) (91 : Basis) where
  plus := ![v4641_pa,v4641_pb,v4641_pg]
  minus := ![(Primitive.Addresses.material4641 1).one,v4641_mb,v4641_mg]
  upper := v4641_upper
  lower := (Primitive.Addresses.material4641 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4641_pa_checked.trans (by decide +kernel)
    · exact v4641_pb_checked.trans (by decide +kernel)
    · exact v4641_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 82 91 Primitive.Addresses.material4641
    · exact v4641_mb_checked.trans (by decide +kernel)
    · exact v4641_mg_checked.trans (by decide +kernel)
  upper_error := v4641_upper_checked
  lower_error := reuse_lower_error 82 91 Primitive.Addresses.material4641

def v4642_pa : Scalar.QComplex := ((999996988082627328102000743088 : Int)/10^30,(-2454348319553998471481425774 : Int)/10^30)
theorem v4642_pa_checked : Scalar.distance (sourceCoefficient 82 92 1 0) v4642_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4642_pb : Scalar.QComplex := ((-1058996118077967111465666 : Int)/10^30,(-431476217141664933973387248 : Int)/10^30)
theorem v4642_pb_checked : Scalar.distance (sourceCoefficient 82 92 1 1) v4642_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4642_pg : Scalar.QComplex := ((-93086149066190883520858 : Int)/10^30,(228466521656644250569 : Int)/10^30)
theorem v4642_pg_checked : Scalar.distance (sourceCoefficient 82 92 1 2) v4642_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4642_mb : Scalar.QComplex := ((-1431340266191136275131253 : Int)/10^30,(-431475142617395368183790609 : Int)/10^30)
theorem v4642_mb_checked : Scalar.distance (sourceCoefficient 82 92 3 1) v4642_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4642_mg : Scalar.QComplex := ((-93085917249644899479538 : Int)/10^30,(308795590787716449373 : Int)/10^30)
theorem v4642_mg_checked : Scalar.distance (sourceCoefficient 82 92 3 2) v4642_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4642_upper : Scalar.QComplex := ((999991262722038666968121438709 : Int)/10^30,(-4180248746502998493689144211 : Int)/10^30)
theorem v4642_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 82 92 5) 1) 14) v4642_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4642 : Material (82 : Basis) (92 : Basis) where
  plus := ![v4642_pa,v4642_pb,v4642_pg]
  minus := ![(Primitive.Addresses.material4642 1).one,v4642_mb,v4642_mg]
  upper := v4642_upper
  lower := (Primitive.Addresses.material4642 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4642_pa_checked.trans (by decide +kernel)
    · exact v4642_pb_checked.trans (by decide +kernel)
    · exact v4642_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 82 92 Primitive.Addresses.material4642
    · exact v4642_mb_checked.trans (by decide +kernel)
    · exact v4642_mg_checked.trans (by decide +kernel)
  upper_error := v4642_upper_checked
  lower_error := reuse_lower_error 82 92 Primitive.Addresses.material4642

def v4643_pa : Scalar.QComplex := ((999996894280792161253231465286 : Int)/10^30,(-2492273815250983934017235639 : Int)/10^30)
theorem v4643_pa_checked : Scalar.distance (sourceCoefficient 82 93 1 0) v4643_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4643_pb : Scalar.QComplex := ((-1075360113205529092681800 : Int)/10^30,(-431476175233449049708904755 : Int)/10^30)
theorem v4643_pb_checked : Scalar.distance (sourceCoefficient 82 93 1 1) v4643_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4643_pg : Scalar.QComplex := ((-93086140179738422639938 : Int)/10^30,(231996870249880683488 : Int)/10^30)
theorem v4643_pg_checked : Scalar.distance (sourceCoefficient 82 93 1 2) v4643_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4643_mb : Scalar.QComplex := ((-1447704219060732166689906 : Int)/10^30,(-431475086587804300158952337 : Int)/10^30)
theorem v4643_mb_checked : Scalar.distance (sourceCoefficient 82 93 3 1) v4643_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4643_mg : Scalar.QComplex := ((-93085905316663912466205 : Int)/10^30,(312325930397834513350 : Int)/10^30)
theorem v4643_mg_checked : Scalar.distance (sourceCoefficient 82 93 3 2) v4643_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4643_upper : Scalar.QComplex := ((999991103464378208030527894079 : Int)/10^30,(-4218174023820955295271016597 : Int)/10^30)
theorem v4643_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 82 93 5) 1) 14) v4643_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4643 : Material (82 : Basis) (93 : Basis) where
  plus := ![v4643_pa,v4643_pb,v4643_pg]
  minus := ![(Primitive.Addresses.material4643 1).one,v4643_mb,v4643_mg]
  upper := v4643_upper
  lower := (Primitive.Addresses.material4643 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4643_pa_checked.trans (by decide +kernel)
    · exact v4643_pb_checked.trans (by decide +kernel)
    · exact v4643_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 82 93 Primitive.Addresses.material4643
    · exact v4643_mb_checked.trans (by decide +kernel)
    · exact v4643_mg_checked.trans (by decide +kernel)
  upper_error := v4643_upper_checked
  lower_error := reuse_lower_error 82 93 Primitive.Addresses.material4643

def v4644_pa : Scalar.QComplex := ((999996781627068127958686495538 : Int)/10^30,(-2537072231100201455273388710 : Int)/10^30)
theorem v4644_pa_checked : Scalar.distance (sourceCoefficient 82 94 1 0) v4644_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4644_pb : Scalar.QComplex := ((-1094689617388570271928767 : Int)/10^30,(-431476124664541461210614843 : Int)/10^30)
theorem v4644_pb_checked : Scalar.distance (sourceCoefficient 82 94 1 1) v4644_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4644_pg : Scalar.QComplex := ((-93086129481634956138316 : Int)/10^30,(236166994281915635834 : Int)/10^30)
theorem v4644_pg_checked : Scalar.distance (sourceCoefficient 82 94 1 2) v4644_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4644_mb : Scalar.QComplex := ((-1467033672407825826786073 : Int)/10^30,(-431475019338423999362913654 : Int)/10^30)
theorem v4644_mb_checked : Scalar.distance (sourceCoefficient 82 94 3 1) v4644_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4644_mg : Scalar.QComplex := ((-93085891019935205125634 : Int)/10^30,(316496043645160237589 : Int)/10^30)
theorem v4644_mg_checked : Scalar.distance (sourceCoefficient 82 94 3 2) v4644_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4644_upper : Scalar.QComplex := ((999990913492820284014238878651 : Int)/10^30,(-4262972178518086985250871681 : Int)/10^30)
theorem v4644_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 82 94 5) 1) 14) v4644_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4644 : Material (82 : Basis) (94 : Basis) where
  plus := ![v4644_pa,v4644_pb,v4644_pg]
  minus := ![(Primitive.Addresses.material4644 1).one,v4644_mb,v4644_mg]
  upper := v4644_upper
  lower := (Primitive.Addresses.material4644 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4644_pa_checked.trans (by decide +kernel)
    · exact v4644_pb_checked.trans (by decide +kernel)
    · exact v4644_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 82 94 Primitive.Addresses.material4644
    · exact v4644_mb_checked.trans (by decide +kernel)
    · exact v4644_mg_checked.trans (by decide +kernel)
  upper_error := v4644_upper_checked
  lower_error := reuse_lower_error 82 94 Primitive.Addresses.material4644

def v4645_pa : Scalar.QComplex := ((999996668320064441395058797823 : Int)/10^30,(-2581346309782168084716794563 : Int)/10^30)
theorem v4645_pa_checked : Scalar.distance (sourceCoefficient 82 95 1 0) v4645_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4645_pb : Scalar.QComplex := ((-1113792881027035097211663 : Int)/10^30,(-431476073553118206339149755 : Int)/10^30)
theorem v4645_pb_checked : Scalar.distance (sourceCoefficient 82 95 1 1) v4645_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4645_pg : Scalar.QComplex := ((-93086118694604922823706 : Int)/10^30,(240288309548002977294 : Int)/10^30)
theorem v4645_pg_checked : Scalar.distance (sourceCoefficient 82 95 1 2) v4645_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4645_mb : Scalar.QComplex := ((-1486136884826416241286153 : Int)/10^30,(-431474951741763634670594194 : Int)/10^30)
theorem v4645_mb_checked : Scalar.distance (sourceCoefficient 82 95 3 1) v4645_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4645_mg : Scalar.QComplex := ((-93085876676399730831072 : Int)/10^30,(320617348067972463120 : Int)/10^30)
theorem v4645_mg_checked : Scalar.distance (sourceCoefficient 82 95 3 2) v4645_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4645_upper : Scalar.QComplex := ((999990723772942062890974217769 : Int)/10^30,(-4307245995701404984592601913 : Int)/10^30)
theorem v4645_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 82 95 5) 1) 14) v4645_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4645 : Material (82 : Basis) (95 : Basis) where
  plus := ![v4645_pa,v4645_pb,v4645_pg]
  minus := ![(Primitive.Addresses.material4645 1).one,v4645_mb,v4645_mg]
  upper := v4645_upper
  lower := (Primitive.Addresses.material4645 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4645_pa_checked.trans (by decide +kernel)
    · exact v4645_pb_checked.trans (by decide +kernel)
    · exact v4645_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 82 95 Primitive.Addresses.material4645
    · exact v4645_mb_checked.trans (by decide +kernel)
    · exact v4645_mg_checked.trans (by decide +kernel)
  upper_error := v4645_upper_checked
  lower_error := reuse_lower_error 82 95 Primitive.Addresses.material4645

def v4646_pa : Scalar.QComplex := ((999996613203986880080628618254 : Int)/10^30,(-2602610335000728505672061286 : Int)/10^30)
theorem v4646_pa_checked : Scalar.distance (sourceCoefficient 82 96 1 0) v4646_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4646_pb : Scalar.QComplex := ((-1122967826665959120951025 : Int)/10^30,(-431476048604366498064808541 : Int)/10^30)
theorem v4646_pb_checked : Scalar.distance (sourceCoefficient 82 96 1 1) v4646_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4646_pg : Scalar.QComplex := ((-93086113438118968285879 : Int)/10^30,(242267701390383800261 : Int)/10^30)
theorem v4646_pg_checked : Scalar.distance (sourceCoefficient 82 96 1 2) v4646_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4646_mb : Scalar.QComplex := ((-1495311805519439613748117 : Int)/10^30,(-431474918875456353777269110 : Int)/10^30)
theorem v4646_mb_checked : Scalar.distance (sourceCoefficient 82 96 3 1) v4646_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4646_mg : Scalar.QComplex := ((-93085869711789722047783 : Int)/10^30,(322596734637224605066 : Int)/10^30)
theorem v4646_mg_checked : Scalar.distance (sourceCoefficient 82 96 3 2) v4646_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4646_upper : Scalar.QComplex := ((999990631957168120563254919319 : Int)/10^30,(-4328509894124347911037620911 : Int)/10^30)
theorem v4646_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 82 96 5) 1) 14) v4646_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4646 : Material (82 : Basis) (96 : Basis) where
  plus := ![v4646_pa,v4646_pb,v4646_pg]
  minus := ![(Primitive.Addresses.material4646 1).one,v4646_mb,v4646_mg]
  upper := v4646_upper
  lower := (Primitive.Addresses.material4646 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4646_pa_checked.trans (by decide +kernel)
    · exact v4646_pb_checked.trans (by decide +kernel)
    · exact v4646_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 82 96 Primitive.Addresses.material4646
    · exact v4646_mb_checked.trans (by decide +kernel)
    · exact v4646_mg_checked.trans (by decide +kernel)
  upper_error := v4646_upper_checked
  lower_error := reuse_lower_error 82 96 Primitive.Addresses.material4646

def v4647_pa : Scalar.QComplex := ((999996420114882157126751492196 : Int)/10^30,(-2675772303487030554127071939 : Int)/10^30)
theorem v4647_pa_checked : Scalar.distance (sourceCoefficient 82 97 1 0) v4647_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4647_pb : Scalar.QComplex := ((-1154535558573111384073776 : Int)/10^30,(-431475960777334218304577113 : Int)/10^30)
theorem v4647_pb_checked : Scalar.distance (sourceCoefficient 82 97 1 1) v4647_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4647_pg : Scalar.QComplex := ((-93086094977283282306724 : Int)/10^30,(249078086450912659802 : Int)/10^30)
theorem v4647_pg_checked : Scalar.distance (sourceCoefficient 82 97 1 2) v4647_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4647_mb : Scalar.QComplex := ((-1526879449881709296480946 : Int)/10^30,(-431474803806925898029611285 : Int)/10^30)
theorem v4647_mb_checked : Scalar.distance (sourceCoefficient 82 97 3 1) v4647_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4647_mg : Scalar.QComplex := ((-93085845373905331001884 : Int)/10^30,(329407101231066104773 : Int)/10^30)
theorem v4647_mg_checked : Scalar.distance (sourceCoefficient 82 97 3 2) v4647_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4647_upper : Scalar.QComplex := ((999990312597430575725788537911 : Int)/10^30,(-4401671420390214262601861531 : Int)/10^30)
theorem v4647_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 82 97 5) 1) 14) v4647_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4647 : Material (82 : Basis) (97 : Basis) where
  plus := ![v4647_pa,v4647_pb,v4647_pg]
  minus := ![(Primitive.Addresses.material4647 1).one,v4647_mb,v4647_mg]
  upper := v4647_upper
  lower := (Primitive.Addresses.material4647 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4647_pa_checked.trans (by decide +kernel)
    · exact v4647_pb_checked.trans (by decide +kernel)
    · exact v4647_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 82 97 Primitive.Addresses.material4647
    · exact v4647_mb_checked.trans (by decide +kernel)
    · exact v4647_mg_checked.trans (by decide +kernel)
  upper_error := v4647_upper_checked
  lower_error := reuse_lower_error 82 97 Primitive.Addresses.material4647

def v4648_pa : Scalar.QComplex := ((999997417775288124829720473752 : Int)/10^30,(-2272541035023543406609107736 : Int)/10^30)
theorem v4648_pa_checked : Scalar.distance (sourceCoefficient 83 84 1 0) v4648_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4648_pb : Scalar.QComplex := ((-980550371962426271556935 : Int)/10^30,(-431476406739940837769556460 : Int)/10^30)
theorem v4648_pb_checked : Scalar.distance (sourceCoefficient 83 84 1 1) v4648_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4648_pg : Scalar.QComplex := ((-93086189517318223153341 : Int)/10^30,(211542731722953543869 : Int)/10^30)
theorem v4648_pg_checked : Scalar.distance (sourceCoefficient 83 84 1 2) v4648_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4648_mb : Scalar.QComplex := ((-1352894712899304777364744 : Int)/10^30,(-431475399910746508337019508 : Int)/10^30)
theorem v4648_mb_checked : Scalar.distance (sourceCoefficient 83 84 3 1) v4648_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4648_mg : Scalar.QComplex := ((-93085972305225670879979 : Int)/10^30,(291871842063027233354 : Int)/10^30)
theorem v4648_mg_checked : Scalar.distance (sourceCoefficient 83 84 3 2) v4648_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4648_upper : Scalar.QComplex := ((999992006196939158505258287661 : Int)/10^30,(-3998442474363688274541164064 : Int)/10^30)
theorem v4648_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 83 84 5) 1) 14) v4648_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4648 : Material (83 : Basis) (84 : Basis) where
  plus := ![v4648_pa,v4648_pb,v4648_pg]
  minus := ![(Primitive.Addresses.material4648 1).one,v4648_mb,v4648_mg]
  upper := v4648_upper
  lower := (Primitive.Addresses.material4648 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4648_pa_checked.trans (by decide +kernel)
    · exact v4648_pb_checked.trans (by decide +kernel)
    · exact v4648_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 83 84 Primitive.Addresses.material4648
    · exact v4648_mb_checked.trans (by decide +kernel)
    · exact v4648_mg_checked.trans (by decide +kernel)
  upper_error := v4648_upper_checked
  lower_error := reuse_lower_error 83 84 Primitive.Addresses.material4648

def v4649_pa : Scalar.QComplex := ((999997234990444446942110108665 : Int)/10^30,(-2351597641142777103390443255 : Int)/10^30)
theorem v4649_pa_checked : Scalar.distance (sourceCoefficient 83 85 1 0) v4649_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4649_pb : Scalar.QComplex := ((-1014661518385952166406782 : Int)/10^30,(-431476327023392024707494546 : Int)/10^30)
theorem v4649_pb_checked : Scalar.distance (sourceCoefficient 83 85 1 1) v4649_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4649_pg : Scalar.QComplex := ((-93086172410948838987507 : Int)/10^30,(218901828730245313564 : Int)/10^30)
theorem v4649_pg_checked : Scalar.distance (sourceCoefficient 83 85 1 2) v4649_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4649_mb : Scalar.QComplex := ((-1387005777829900576738113 : Int)/10^30,(-431475290757844322890904323 : Int)/10^30)
theorem v4649_mb_checked : Scalar.distance (sourceCoefficient 83 85 3 1) v4649_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4649_mg : Scalar.QComplex := ((-93085948848293380329994 : Int)/10^30,(299230921568164523628 : Int)/10^30)
theorem v4649_mg_checked : Scalar.distance (sourceCoefficient 83 85 3 2) v4649_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4649_upper : Scalar.QComplex := ((999991686967837514656394953577 : Int)/10^30,(-4077498647267335721481741025 : Int)/10^30)
theorem v4649_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 83 85 5) 1) 14) v4649_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4649 : Material (83 : Basis) (85 : Basis) where
  plus := ![v4649_pa,v4649_pb,v4649_pg]
  minus := ![(Primitive.Addresses.material4649 1).one,v4649_mb,v4649_mg]
  upper := v4649_upper
  lower := (Primitive.Addresses.material4649 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4649_pa_checked.trans (by decide +kernel)
    · exact v4649_pb_checked.trans (by decide +kernel)
    · exact v4649_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 83 85 Primitive.Addresses.material4649
    · exact v4649_mb_checked.trans (by decide +kernel)
    · exact v4649_mg_checked.trans (by decide +kernel)
  upper_error := v4649_upper_checked
  lower_error := reuse_lower_error 83 85 Primitive.Addresses.material4649

def v4650_pa : Scalar.QComplex := ((999997200586874156582070478569 : Int)/10^30,(-2366182244666075317354789811 : Int)/10^30)
theorem v4650_pa_checked : Scalar.distance (sourceCoefficient 83 86 1 0) v4650_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4650_pb : Scalar.QComplex := ((-1020954446342288059286486 : Int)/10^30,(-431476311924185988055190834 : Int)/10^30)
theorem v4650_pb_checked : Scalar.distance (sourceCoefficient 83 86 1 1) v4650_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4650_pg : Scalar.QComplex := ((-93086169180953998960080 : Int)/10^30,(220259457337171735826 : Int)/10^30)
theorem v4650_pg_checked : Scalar.distance (sourceCoefficient 83 86 1 2) v4650_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4650_mb : Scalar.QComplex := ((-1393298690413157023823151 : Int)/10^30,(-431475270228130504999199072 : Int)/10^30)
theorem v4650_mb_checked : Scalar.distance (sourceCoefficient 83 86 3 1) v4650_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4650_mg : Scalar.QComplex := ((-93085944446727400522395 : Int)/10^30,(300588546882243695462 : Int)/10^30)
theorem v4650_mg_checked : Scalar.distance (sourceCoefficient 83 86 3 2) v4650_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4650_upper : Scalar.QComplex := ((999991627392615888056363620994 : Int)/10^30,(-4092083169691138961725810527 : Int)/10^30)
theorem v4650_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 83 86 5) 1) 14) v4650_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4650 : Material (83 : Basis) (86 : Basis) where
  plus := ![v4650_pa,v4650_pb,v4650_pg]
  minus := ![(Primitive.Addresses.material4650 1).one,v4650_mb,v4650_mg]
  upper := v4650_upper
  lower := (Primitive.Addresses.material4650 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4650_pa_checked.trans (by decide +kernel)
    · exact v4650_pb_checked.trans (by decide +kernel)
    · exact v4650_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 83 86 Primitive.Addresses.material4650
    · exact v4650_mb_checked.trans (by decide +kernel)
    · exact v4650_mg_checked.trans (by decide +kernel)
  upper_error := v4650_upper_checked
  lower_error := reuse_lower_error 83 86 Primitive.Addresses.material4650

def v4651_pa : Scalar.QComplex := ((999997198301252073153228845915 : Int)/10^30,(-2367147998401836176887367701 : Int)/10^30)
theorem v4651_pa_checked : Scalar.distance (sourceCoefficient 83 87 1 0) v4651_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4651_pb : Scalar.QComplex := ((-1021371147326437860410611 : Int)/10^30,(-431476310920036709984000870 : Int)/10^30)
theorem v4651_pb_checked : Scalar.distance (sourceCoefficient 83 87 1 1) v4651_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4651_pg : Scalar.QComplex := ((-93086168966256833711382 : Int)/10^30,(220349355899884514926 : Int)/10^30)
theorem v4651_pg_checked : Scalar.distance (sourceCoefficient 83 87 1 2) v4651_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4651_mb : Scalar.QComplex := ((-1393715390375614402601737 : Int)/10^30,(-431475268864387419013042031 : Int)/10^30)
theorem v4651_mb_checked : Scalar.distance (sourceCoefficient 83 87 3 1) v4651_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4651_mg : Scalar.QComplex := ((-93085944154451904475099 : Int)/10^30,(300678445226209147088 : Int)/10^30)
theorem v4651_mg_checked : Scalar.distance (sourceCoefficient 83 87 3 2) v4651_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4651_upper : Scalar.QComplex := ((999991623440193873364400648497 : Int)/10^30,(-4093048918043746711262994093 : Int)/10^30)
theorem v4651_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 83 87 5) 1) 14) v4651_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4651 : Material (83 : Basis) (87 : Basis) where
  plus := ![v4651_pa,v4651_pb,v4651_pg]
  minus := ![(Primitive.Addresses.material4651 1).one,v4651_mb,v4651_mg]
  upper := v4651_upper
  lower := (Primitive.Addresses.material4651 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4651_pa_checked.trans (by decide +kernel)
    · exact v4651_pb_checked.trans (by decide +kernel)
    · exact v4651_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 83 87 Primitive.Addresses.material4651
    · exact v4651_mb_checked.trans (by decide +kernel)
    · exact v4651_mg_checked.trans (by decide +kernel)
  upper_error := v4651_upper_checked
  lower_error := reuse_lower_error 83 87 Primitive.Addresses.material4651

def v4652_pa : Scalar.QComplex := ((999997170395409900435799975118 : Int)/10^30,(-2378907558846495423764271266 : Int)/10^30)
theorem v4652_pa_checked : Scalar.distance (sourceCoefficient 83 88 1 0) v4652_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4652_pb : Scalar.QComplex := ((-1026445132755225755631749 : Int)/10^30,(-431476298649904879497854365 : Int)/10^30)
theorem v4652_pb_checked : Scalar.distance (sourceCoefficient 83 88 1 1) v4652_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4652_pg : Scalar.QComplex := ((-93086166343857645617528 : Int)/10^30,(221444011338436127160 : Int)/10^30)
theorem v4652_pg_checked : Scalar.distance (sourceCoefficient 83 88 1 2) v4652_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4652_mb : Scalar.QComplex := ((-1398789363326554486608970 : Int)/10^30,(-431475252215639256034304801 : Int)/10^30)
theorem v4652_mb_checked : Scalar.distance (sourceCoefficient 83 88 3 1) v4652_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4652_mg : Scalar.QComplex := ((-93085940587415350801068 : Int)/10^30,(301773097994158120475 : Int)/10^30)
theorem v4652_mg_checked : Scalar.distance (sourceCoefficient 83 88 3 2) v4652_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4652_upper : Scalar.QComplex := ((999991575238458754628984306485 : Int)/10^30,(-4104808412810970058941947401 : Int)/10^30)
theorem v4652_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 83 88 5) 1) 14) v4652_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4652 : Material (83 : Basis) (88 : Basis) where
  plus := ![v4652_pa,v4652_pb,v4652_pg]
  minus := ![(Primitive.Addresses.material4652 1).one,v4652_mb,v4652_mg]
  upper := v4652_upper
  lower := (Primitive.Addresses.material4652 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4652_pa_checked.trans (by decide +kernel)
    · exact v4652_pb_checked.trans (by decide +kernel)
    · exact v4652_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 83 88 Primitive.Addresses.material4652
    · exact v4652_mb_checked.trans (by decide +kernel)
    · exact v4652_mg_checked.trans (by decide +kernel)
  upper_error := v4652_upper_checked
  lower_error := reuse_lower_error 83 88 Primitive.Addresses.material4652

def v4653_pa : Scalar.QComplex := ((999997131990578152006850547110 : Int)/10^30,(-2394996997538398270224633312 : Int)/10^30)
theorem v4653_pa_checked : Scalar.distance (sourceCoefficient 83 89 1 0) v4653_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4653_pb : Scalar.QComplex := ((-1033387363024288646252504 : Int)/10^30,(-431476281733011705405574663 : Int)/10^30)
theorem v4653_pb_checked : Scalar.distance (sourceCoefficient 83 89 1 1) v4653_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4653_pg : Scalar.QComplex := ((-93086162731558439429168 : Int)/10^30,(222941719653405697521 : Int)/10^30)
theorem v4653_pg_checked : Scalar.distance (sourceCoefficient 83 89 1 2) v4653_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4653_mb : Scalar.QComplex := ((-1405731576412190871804130 : Int)/10^30,(-431475229307920325117814011 : Int)/10^30)
theorem v4653_mb_checked : Scalar.distance (sourceCoefficient 83 89 3 1) v4653_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4653_mg : Scalar.QComplex := ((-93085935682662668096538 : Int)/10^30,(303270802634210913497 : Int)/10^30)
theorem v4653_mg_checked : Scalar.distance (sourceCoefficient 83 89 3 2) v4653_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4653_upper : Scalar.QComplex := ((999991509064772645937447093379 : Int)/10^30,(-4120897761256288433378779758 : Int)/10^30)
theorem v4653_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 83 89 5) 1) 14) v4653_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4653 : Material (83 : Basis) (89 : Basis) where
  plus := ![v4653_pa,v4653_pb,v4653_pg]
  minus := ![(Primitive.Addresses.material4653 1).one,v4653_mb,v4653_mg]
  upper := v4653_upper
  lower := (Primitive.Addresses.material4653 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4653_pa_checked.trans (by decide +kernel)
    · exact v4653_pb_checked.trans (by decide +kernel)
    · exact v4653_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 83 89 Primitive.Addresses.material4653
    · exact v4653_mb_checked.trans (by decide +kernel)
    · exact v4653_mg_checked.trans (by decide +kernel)
  upper_error := v4653_upper_checked
  lower_error := reuse_lower_error 83 89 Primitive.Addresses.material4653

def v4654_pa : Scalar.QComplex := ((999997068891315413596231299018 : Int)/10^30,(-2421199863244396988573598851 : Int)/10^30)
theorem v4654_pa_checked : Scalar.distance (sourceCoefficient 83 90 1 0) v4654_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4654_pb : Scalar.QComplex := ((-1044693308957872549332599 : Int)/10^30,(-431476253863801922955897370 : Int)/10^30)
theorem v4654_pb_checked : Scalar.distance (sourceCoefficient 83 90 1 1) v4654_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4654_pg : Scalar.QComplex := ((-93086156788481364067901 : Int)/10^30,(225380850701986407120 : Int)/10^30)
theorem v4654_pg_checked : Scalar.distance (sourceCoefficient 83 90 1 2) v4654_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4654_mb : Scalar.QComplex := ((-1417037494086181536915879 : Int)/10^30,(-431475191682198779868138779 : Int)/10^30)
theorem v4654_mb_checked : Scalar.distance (sourceCoefficient 83 90 3 1) v4654_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4654_mg : Scalar.QComplex := ((-93085927634727565073768 : Int)/10^30,(305709927645983810133 : Int)/10^30)
theorem v4654_mg_checked : Scalar.distance (sourceCoefficient 83 90 3 2) v4654_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4654_upper : Scalar.QComplex := ((999991400741834783320648550467 : Int)/10^30,(-4147100479032593521369489715 : Int)/10^30)
theorem v4654_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 83 90 5) 1) 14) v4654_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4654 : Material (83 : Basis) (90 : Basis) where
  plus := ![v4654_pa,v4654_pb,v4654_pg]
  minus := ![(Primitive.Addresses.material4654 1).one,v4654_mb,v4654_mg]
  upper := v4654_upper
  lower := (Primitive.Addresses.material4654 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4654_pa_checked.trans (by decide +kernel)
    · exact v4654_pb_checked.trans (by decide +kernel)
    · exact v4654_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 83 90 Primitive.Addresses.material4654
    · exact v4654_mb_checked.trans (by decide +kernel)
    · exact v4654_mg_checked.trans (by decide +kernel)
  upper_error := v4654_upper_checked
  lower_error := reuse_lower_error 83 90 Primitive.Addresses.material4654

def v4655_pa : Scalar.QComplex := ((999997033042868068689756699807 : Int)/10^30,(-2435960890701654464584152371 : Int)/10^30)
theorem v4655_pa_checked : Scalar.distance (sourceCoefficient 83 91 1 0) v4655_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4655_pb : Scalar.QComplex := ((-1051062359467992044021610 : Int)/10^30,(-431476237990126880552815461 : Int)/10^30)
theorem v4655_pb_checked : Scalar.distance (sourceCoefficient 83 91 1 1) v4655_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4655_pg : Scalar.QComplex := ((-93086153407695805266807 : Int)/10^30,(226754901939075030300 : Int)/10^30)
theorem v4655_pg_checked : Scalar.distance (sourceCoefficient 83 91 1 2) v4655_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4655_mb : Scalar.QComplex := ((-1423406528526545808890278 : Int)/10^30,(-431475170312325909113165807 : Int)/10^30)
theorem v4655_mb_checked : Scalar.distance (sourceCoefficient 83 91 3 1) v4655_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4655_mg : Scalar.QComplex := ((-93085923068198932456606 : Int)/10^30,(307083975453984688185 : Int)/10^30)
theorem v4655_mg_checked : Scalar.distance (sourceCoefficient 83 91 3 2) v4655_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4655_upper : Scalar.QComplex := ((999991339417246549189405683911 : Int)/10^30,(-4161861422633866580313839460 : Int)/10^30)
theorem v4655_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 83 91 5) 1) 14) v4655_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4655 : Material (83 : Basis) (91 : Basis) where
  plus := ![v4655_pa,v4655_pb,v4655_pg]
  minus := ![(Primitive.Addresses.material4655 1).one,v4655_mb,v4655_mg]
  upper := v4655_upper
  lower := (Primitive.Addresses.material4655 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4655_pa_checked.trans (by decide +kernel)
    · exact v4655_pb_checked.trans (by decide +kernel)
    · exact v4655_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 83 91 Primitive.Addresses.material4655
    · exact v4655_mb_checked.trans (by decide +kernel)
    · exact v4655_mg_checked.trans (by decide +kernel)
  upper_error := v4655_upper_checked
  lower_error := reuse_lower_error 83 91 Primitive.Addresses.material4655

def v4656_pa : Scalar.QComplex := ((999996954688452165765731011635 : Int)/10^30,(-2467916899278832112401542455 : Int)/10^30)
theorem v4656_pa_checked : Scalar.distance (sourceCoefficient 83 92 1 0) v4656_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4656_pb : Scalar.QComplex := ((-1064850656305885025542583 : Int)/10^30,(-431476203195922618130070741 : Int)/10^30)
theorem v4656_pb_checked : Scalar.distance (sourceCoefficient 83 92 1 1) v4656_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4656_pg : Scalar.QComplex := ((-93086146007599959787302 : Int)/10^30,(229729572419012496557 : Int)/10^30)
theorem v4656_pg_checked : Scalar.distance (sourceCoefficient 83 92 1 2) v4656_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4656_mb : Scalar.QComplex := ((-1437194790204594515684524 : Int)/10^30,(-431475123619455432898105539 : Int)/10^30)
theorem v4656_mb_checked : Scalar.distance (sourceCoefficient 83 92 3 1) v4656_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4656_mg : Scalar.QComplex := ((-93085913101099192370012 : Int)/10^30,(310058638440366958900 : Int)/10^30)
theorem v4656_mg_checked : Scalar.distance (sourceCoefficient 83 92 3 2) v4656_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4656_upper : Scalar.QComplex := ((999991205909775568207260704857 : Int)/10^30,(-4193817248383709677521010322 : Int)/10^30)
theorem v4656_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 83 92 5) 1) 14) v4656_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4656 : Material (83 : Basis) (92 : Basis) where
  plus := ![v4656_pa,v4656_pb,v4656_pg]
  minus := ![(Primitive.Addresses.material4656 1).one,v4656_mb,v4656_mg]
  upper := v4656_upper
  lower := (Primitive.Addresses.material4656 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4656_pa_checked.trans (by decide +kernel)
    · exact v4656_pb_checked.trans (by decide +kernel)
    · exact v4656_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 83 92 Primitive.Addresses.material4656
    · exact v4656_mb_checked.trans (by decide +kernel)
    · exact v4656_mg_checked.trans (by decide +kernel)
  upper_error := v4656_upper_checked
  lower_error := reuse_lower_error 83 92 Primitive.Addresses.material4656

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
