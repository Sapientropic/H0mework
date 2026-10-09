import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B138

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3313_pa : Scalar.QComplex := ((999998428352443861624642844605 : Int)/10^30,(-1772933343981298694155170850 : Int)/10^30)
theorem v3313_pa_checked : Scalar.distance (sourceCoefficient 43 89 1 0) v3313_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3313_pb : Scalar.QComplex := ((-764980806658924402385518 : Int)/10^30,(-431476799156403199617376432 : Int)/10^30)
theorem v3313_pb_checked : Scalar.distance (sourceCoefficient 43 89 1 1) v3313_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3313_pg : Scalar.QComplex := ((-93086278882550565770542 : Int)/10^30,(165036027076484752393 : Int)/10^30)
theorem v3313_pg_checked : Scalar.distance (sourceCoefficient 43 89 1 2) v3313_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3313_mb : Scalar.QComplex := ((-1137325566499937323412395 : Int)/10^30,(-431475978353888719713469616 : Int)/10^30)
theorem v3313_mb_checked : Scalar.distance (sourceCoefficient 43 89 3 1) v3313_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3313_mg : Scalar.QComplex := ((-93086101803616264416897 : Int)/10^30,(245365231851300694184 : Int)/10^30)
theorem v3313_mg_checked : Scalar.distance (sourceCoefficient 43 89 3 2) v3313_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3313_upper : Scalar.QComplex := ((999993879050140442572556801679 : Int)/10^30,(-3498837271592903285806224335 : Int)/10^30)
theorem v3313_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 89 5) 1) 14) v3313_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3313 : Material (43 : Basis) (89 : Basis) where
  plus := ![v3313_pa,v3313_pb,v3313_pg]
  minus := ![(Primitive.Addresses.material3313 1).one,v3313_mb,v3313_mg]
  upper := v3313_upper
  lower := (Primitive.Addresses.material3313 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3313_pa_checked.trans (by decide +kernel)
    · exact v3313_pb_checked.trans (by decide +kernel)
    · exact v3313_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 89 Primitive.Addresses.material3313
    · exact v3313_mb_checked.trans (by decide +kernel)
    · exact v3313_mg_checked.trans (by decide +kernel)
  upper_error := v3313_upper_checked
  lower_error := reuse_lower_error 43 89 Primitive.Addresses.material3313

def v3314_pa : Scalar.QComplex := ((999998381553078312634284333038 : Int)/10^30,(-1799136243869344407473000591 : Int)/10^30)
theorem v3314_pa_checked : Scalar.distance (sourceCoefficient 43 90 1 0) v3314_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3314_pb : Scalar.QComplex := ((-776286762425031265793388 : Int)/10^30,(-431476775975886085354692987 : Int)/10^30)
theorem v3314_pb_checked : Scalar.distance (sourceCoefficient 43 90 1 1) v3314_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3314_pg : Scalar.QComplex := ((-93086274203889500444117 : Int)/10^30,(167475160776636021751 : Int)/10^30)
theorem v3314_pg_checked : Scalar.distance (sourceCoefficient 43 90 1 2) v3314_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3314_mb : Scalar.QComplex := ((-1148631498052577889520884 : Int)/10^30,(-431475945416849611811749659 : Int)/10^30)
theorem v3314_mb_checked : Scalar.distance (sourceCoefficient 43 90 3 1) v3314_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3314_mg : Scalar.QComplex := ((-93086095020094412443131 : Int)/10^30,(247804360605777232754 : Int)/10^30)
theorem v3314_mg_checked : Scalar.distance (sourceCoefficient 43 90 3 2) v3314_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3314_upper : Scalar.QComplex := ((999993787027016497481733543124 : Int)/10^30,(-3525040051683348292439539239 : Int)/10^30)
theorem v3314_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 90 5) 1) 14) v3314_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3314 : Material (43 : Basis) (90 : Basis) where
  plus := ![v3314_pa,v3314_pb,v3314_pg]
  minus := ![(Primitive.Addresses.material3314 1).one,v3314_mb,v3314_mg]
  upper := v3314_upper
  lower := (Primitive.Addresses.material3314 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3314_pa_checked.trans (by decide +kernel)
    · exact v3314_pb_checked.trans (by decide +kernel)
    · exact v3314_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 90 Primitive.Addresses.material3314
    · exact v3314_mb_checked.trans (by decide +kernel)
    · exact v3314_mg_checked.trans (by decide +kernel)
  upper_error := v3314_upper_checked
  lower_error := reuse_lower_error 43 90 Primitive.Addresses.material3314

def v3315_pa : Scalar.QComplex := ((999998354886956068955641511991 : Int)/10^30,(-1813897290770665825383036874 : Int)/10^30)
theorem v3315_pa_checked : Scalar.distance (sourceCoefficient 43 91 1 0) v3315_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3315_pb : Scalar.QComplex := ((-782655818528268247095302 : Int)/10^30,(-431476762743522199219738016 : Int)/10^30)
theorem v3315_pb_checked : Scalar.distance (sourceCoefficient 43 91 1 1) v3315_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3315_pg : Scalar.QComplex := ((-93086271535395480565205 : Int)/10^30,(168849213522040032166 : Int)/10^30)
theorem v3315_pg_checked : Scalar.distance (sourceCoefficient 43 91 1 2) v3315_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3315_mb : Scalar.QComplex := ((-1155000540365390133155854 : Int)/10^30,(-431475926688282087235559977 : Int)/10^30)
theorem v3315_mb_checked : Scalar.distance (sourceCoefficient 43 91 3 1) v3315_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3315_mg : Scalar.QComplex := ((-93086091165855751921210 : Int)/10^30,(249178410536768454096 : Int)/10^30)
theorem v3315_mg_checked : Scalar.distance (sourceCoefficient 43 91 3 2) v3315_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3315_upper : Scalar.QComplex := ((999993734884706129893303835077 : Int)/10^30,(-3539801030576516444327393215 : Int)/10^30)
theorem v3315_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 91 5) 1) 14) v3315_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3315 : Material (43 : Basis) (91 : Basis) where
  plus := ![v3315_pa,v3315_pb,v3315_pg]
  minus := ![(Primitive.Addresses.material3315 1).one,v3315_mb,v3315_mg]
  upper := v3315_upper
  lower := (Primitive.Addresses.material3315 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3315_pa_checked.trans (by decide +kernel)
    · exact v3315_pb_checked.trans (by decide +kernel)
    · exact v3315_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 91 Primitive.Addresses.material3315
    · exact v3315_mb_checked.trans (by decide +kernel)
    · exact v3315_mg_checked.trans (by decide +kernel)
  upper_error := v3315_upper_checked
  lower_error := reuse_lower_error 43 91 Primitive.Addresses.material3315

def v3316_pa : Scalar.QComplex := ((999998296411268979103936915146 : Int)/10^30,(-1845853341906454838158534762 : Int)/10^30)
theorem v3316_pa_checked : Scalar.distance (sourceCoefficient 43 92 1 0) v3316_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3316_pb : Scalar.QComplex := ((-796444127608216880228518 : Int)/10^30,(-431476733667467477480375600 : Int)/10^30)
theorem v3316_pb_checked : Scalar.distance (sourceCoefficient 43 92 1 1) v3316_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3316_pg : Scalar.QComplex := ((-93086265677332852329747 : Int)/10^30,(171823887303335099497 : Int)/10^30)
theorem v3316_pg_checked : Scalar.distance (sourceCoefficient 43 92 1 2) v3316_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3316_mb : Scalar.QComplex := ((-1168788819219995451000163 : Int)/10^30,(-431475885713548458232810050 : Int)/10^30)
theorem v3316_mb_checked : Scalar.distance (sourceCoefficient 43 92 3 1) v3316_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3316_mg : Scalar.QComplex := ((-93086082740785805986300 : Int)/10^30,(252153078155212312523 : Int)/10^30)
theorem v3316_mg_checked : Scalar.distance (sourceCoefficient 43 92 3 2) v3316_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3316_upper : Scalar.QComplex := ((999993621255860902649703541451 : Int)/10^30,(-3571756933193790067612497941 : Int)/10^30)
theorem v3316_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 92 5) 1) 14) v3316_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3316 : Material (43 : Basis) (92 : Basis) where
  plus := ![v3316_pa,v3316_pb,v3316_pg]
  minus := ![(Primitive.Addresses.material3316 1).one,v3316_mb,v3316_mg]
  upper := v3316_upper
  lower := (Primitive.Addresses.material3316 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3316_pa_checked.trans (by decide +kernel)
    · exact v3316_pb_checked.trans (by decide +kernel)
    · exact v3316_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 92 Primitive.Addresses.material3316
    · exact v3316_mb_checked.trans (by decide +kernel)
    · exact v3316_mg_checked.trans (by decide +kernel)
  upper_error := v3316_upper_checked
  lower_error := reuse_lower_error 43 92 Primitive.Addresses.material3316

def v3317_pa : Scalar.QComplex := ((999998225686977109461801935073 : Int)/10^30,(-1883778887660219318971069083 : Int)/10^30)
theorem v3317_pa_checked : Scalar.distance (sourceCoefficient 43 93 1 0) v3317_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3317_pb : Scalar.QComplex := ((-812808137134694900634147 : Int)/10^30,(-431476698397545432930956449 : Int)/10^30)
theorem v3317_pb_checked : Scalar.distance (sourceCoefficient 43 93 1 1) v3317_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3317_pg : Scalar.QComplex := ((-93086258581052116051820 : Int)/10^30,(175354239779577160685 : Int)/10^30)
theorem v3317_pg_checked : Scalar.distance (sourceCoefficient 43 93 1 2) v3317_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3317_mb : Scalar.QComplex := ((-1185152792217050626391938 : Int)/10^30,(-431475836322236332566814862 : Int)/10^30)
theorem v3317_mb_checked : Scalar.distance (sourceCoefficient 43 93 3 1) v3317_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3317_mg : Scalar.QComplex := ((-93086072597972526154238 : Int)/10^30,(255683423193172130939 : Int)/10^30)
theorem v3317_mg_checked : Scalar.distance (sourceCoefficient 43 93 3 2) v3317_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3317_upper : Scalar.QComplex := ((999993485075622976169411743462 : Int)/10^30,(-3609682300398197486383694355 : Int)/10^30)
theorem v3317_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 93 5) 1) 14) v3317_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3317 : Material (43 : Basis) (93 : Basis) where
  plus := ![v3317_pa,v3317_pb,v3317_pg]
  minus := ![(Primitive.Addresses.material3317 1).one,v3317_mb,v3317_mg]
  upper := v3317_upper
  lower := (Primitive.Addresses.material3317 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3317_pa_checked.trans (by decide +kernel)
    · exact v3317_pb_checked.trans (by decide +kernel)
    · exact v3317_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 93 Primitive.Addresses.material3317
    · exact v3317_mb_checked.trans (by decide +kernel)
    · exact v3317_mg_checked.trans (by decide +kernel)
  upper_error := v3317_upper_checked
  lower_error := reuse_lower_error 43 93 Primitive.Addresses.material3317

def v3318_pa : Scalar.QComplex := ((999998140292946731245651068775 : Int)/10^30,(-1928577363765110855115727749 : Int)/10^30)
theorem v3318_pa_checked : Scalar.distance (sourceCoefficient 43 94 1 0) v3318_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3318_pb : Scalar.QComplex := ((-832137658650381205841356 : Int)/10^30,(-431476655669934175307570564 : Int)/10^30)
theorem v3318_pb_checked : Scalar.distance (sourceCoefficient 43 94 1 1) v3318_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3318_pg : Scalar.QComplex := ((-93086249997538232662926 : Int)/10^30,(179524368485766648175 : Int)/10^30)
theorem v3318_pg_checked : Scalar.distance (sourceCoefficient 43 94 1 2) v3318_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3318_mb : Scalar.QComplex := ((-1204482269663468533380598 : Int)/10^30,(-431475776914134485680580930 : Int)/10^30)
theorem v3318_mb_checked : Scalar.distance (sourceCoefficient 43 94 3 1) v3318_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3318_mg : Scalar.QComplex := ((-93086060415828580983204 : Int)/10^30,(259853542939446222568 : Int)/10^30)
theorem v3318_mg_checked : Scalar.distance (sourceCoefficient 43 94 3 2) v3318_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3318_upper : Scalar.QComplex := ((999993322363614111292968495880 : Int)/10^30,(-3654480562398671716078518384 : Int)/10^30)
theorem v3318_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 94 5) 1) 14) v3318_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3318 : Material (43 : Basis) (94 : Basis) where
  plus := ![v3318_pa,v3318_pb,v3318_pg]
  minus := ![(Primitive.Addresses.material3318 1).one,v3318_mb,v3318_mg]
  upper := v3318_upper
  lower := (Primitive.Addresses.material3318 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3318_pa_checked.trans (by decide +kernel)
    · exact v3318_pb_checked.trans (by decide +kernel)
    · exact v3318_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 94 Primitive.Addresses.material3318
    · exact v3318_mb_checked.trans (by decide +kernel)
    · exact v3318_mg_checked.trans (by decide +kernel)
  upper_error := v3318_upper_checked
  lower_error := reuse_lower_error 43 94 Primitive.Addresses.material3318

def v3319_pa : Scalar.QComplex := ((999998053926579565114411892792 : Int)/10^30,(-1972851503197342385591731211 : Int)/10^30)
theorem v3319_pa_checked : Scalar.distance (sourceCoefficient 43 95 1 0) v3319_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3319_pb : Scalar.QComplex := ((-851240939763760953711838 : Int)/10^30,(-431476612308029891007587439 : Int)/10^30)
theorem v3319_pb_checked : Scalar.distance (sourceCoefficient 43 95 1 1) v3319_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3319_pg : Scalar.QComplex := ((-93086241300347868028575 : Int)/10^30,(183645688464374924773 : Int)/10^30)
theorem v3319_pg_checked : Scalar.distance (sourceCoefficient 43 95 1 2) v3319_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3319_mb : Scalar.QComplex := ((-1223585506244453209983981 : Int)/10^30,(-431475717066975125995122935 : Int)/10^30)
theorem v3319_mb_checked : Scalar.distance (sourceCoefficient 43 95 3 1) v3319_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3319_mg : Scalar.QComplex := ((-93086048162127930532760 : Int)/10^30,(263974853878215139735 : Int)/10^30)
theorem v3319_mg_checked : Scalar.distance (sourceCoefficient 43 95 3 2) v3319_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3319_upper : Scalar.QComplex := ((999993159584227436242666442545 : Int)/10^30,(-3698754486829258734882429745 : Int)/10^30)
theorem v3319_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 95 5) 1) 14) v3319_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3319 : Material (43 : Basis) (95 : Basis) where
  plus := ![v3319_pa,v3319_pb,v3319_pg]
  minus := ![(Primitive.Addresses.material3319 1).one,v3319_mb,v3319_mg]
  upper := v3319_upper
  lower := (Primitive.Addresses.material3319 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3319_pa_checked.trans (by decide +kernel)
    · exact v3319_pb_checked.trans (by decide +kernel)
    · exact v3319_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 95 Primitive.Addresses.material3319
    · exact v3319_mb_checked.trans (by decide +kernel)
    · exact v3319_mg_checked.trans (by decide +kernel)
  upper_error := v3319_upper_checked
  lower_error := reuse_lower_error 43 95 Primitive.Addresses.material3319

def v3320_pa : Scalar.QComplex := ((999998011749594067151417804225 : Int)/10^30,(-1994115558017142714718764597 : Int)/10^30)
theorem v3320_pa_checked : Scalar.distance (sourceCoefficient 43 96 1 0) v3320_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3320_pb : Scalar.QComplex := ((-860415893917530922795261 : Int)/10^30,(-431476591081229551332195182 : Int)/10^30)
theorem v3320_pb_checked : Scalar.distance (sourceCoefficient 43 96 1 1) v3320_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3320_pg : Scalar.QComplex := ((-93086237047573454574640 : Int)/10^30,(185625082602983799422 : Int)/10^30)
theorem v3320_pg_checked : Scalar.distance (sourceCoefficient 43 96 1 2) v3320_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3320_mb : Scalar.QComplex := ((-1232760438664195757957700 : Int)/10^30,(-431475687922610479919594291 : Int)/10^30)
theorem v3320_mb_checked : Scalar.distance (sourceCoefficient 43 96 3 1) v3320_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3320_mg : Scalar.QComplex := ((-93086042201227107564293 : Int)/10^30,(265954243609852332838 : Int)/10^30)
theorem v3320_mg_checked : Scalar.distance (sourceCoefficient 43 96 3 2) v3320_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3320_upper : Scalar.QComplex := ((999993080707475196954009399110 : Int)/10^30,(-3720018437185096558011589283 : Int)/10^30)
theorem v3320_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 96 5) 1) 14) v3320_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3320 : Material (43 : Basis) (96 : Basis) where
  plus := ![v3320_pa,v3320_pb,v3320_pg]
  minus := ![(Primitive.Addresses.material3320 1).one,v3320_mb,v3320_mg]
  upper := v3320_upper
  lower := (Primitive.Addresses.material3320 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3320_pa_checked.trans (by decide +kernel)
    · exact v3320_pb_checked.trans (by decide +kernel)
    · exact v3320_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 96 Primitive.Addresses.material3320
    · exact v3320_mb_checked.trans (by decide +kernel)
    · exact v3320_mg_checked.trans (by decide +kernel)
  upper_error := v3320_upper_checked
  lower_error := reuse_lower_error 43 96 Primitive.Addresses.material3320

def v3321_pa : Scalar.QComplex := ((999997863179316313619916222891 : Int)/10^30,(-2067277630452699001396458299 : Int)/10^30)
theorem v3321_pa_checked : Scalar.distance (sourceCoefficient 43 97 1 0) v3321_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3321_pb : Scalar.QComplex := ((-891983655725859042253821 : Int)/10^30,(-431476516060111862720920253 : Int)/10^30)
theorem v3321_pb_checked : Scalar.distance (sourceCoefficient 43 97 1 1) v3321_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3321_pg : Scalar.QComplex := ((-93086222040153203404740 : Int)/10^30,(192435475727066527557 : Int)/10^30)
theorem v3321_pg_checked : Scalar.distance (sourceCoefficient 43 97 1 2) v3321_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3321_mb : Scalar.QComplex := ((-1264328123978557698630604 : Int)/10^30,(-431475585659964043725566423 : Int)/10^30)
theorem v3321_mb_checked : Scalar.distance (sourceCoefficient 43 97 3 1) v3321_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3321_mg : Scalar.QComplex := ((-93086021316749906979435 : Int)/10^30,(272764621247386682893 : Int)/10^30)
theorem v3321_mg_checked : Scalar.distance (sourceCoefficient 43 97 3 2) v3321_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3321_upper : Scalar.QComplex := ((999992805866318908993083886830 : Int)/10^30,(-3793180144235518960384137910 : Int)/10^30)
theorem v3321_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 43 97 5) 1) 14) v3321_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3321 : Material (43 : Basis) (97 : Basis) where
  plus := ![v3321_pa,v3321_pb,v3321_pg]
  minus := ![(Primitive.Addresses.material3321 1).one,v3321_mb,v3321_mg]
  upper := v3321_upper
  lower := (Primitive.Addresses.material3321 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3321_pa_checked.trans (by decide +kernel)
    · exact v3321_pb_checked.trans (by decide +kernel)
    · exact v3321_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 43 97 Primitive.Addresses.material3321
    · exact v3321_mb_checked.trans (by decide +kernel)
    · exact v3321_mg_checked.trans (by decide +kernel)
  upper_error := v3321_upper_checked
  lower_error := reuse_lower_error 43 97 Primitive.Addresses.material3321

def v3322_pa : Scalar.QComplex := ((999999492070060124945975613446 : Int)/10^30,(-1007898616804926579365996993 : Int)/10^30)
theorem v3322_pa_checked : Scalar.distance (sourceCoefficient 44 45 1 0) v3322_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3322_pb : Scalar.QComplex := ((-434885596598361312188146 : Int)/10^30,(-431477301839691017902532131 : Int)/10^30)
theorem v3322_pb_checked : Scalar.distance (sourceCoefficient 44 45 1 1) v3322_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3322_pg : Scalar.QComplex := ((-93086382615525470725235 : Int)/10^30,(93821683936404566395 : Int)/10^30)
theorem v3322_pg_checked : Scalar.distance (sourceCoefficient 44 45 1 2) v3322_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3322_mb : Scalar.QComplex := ((-807230913141944407464320 : Int)/10^30,(-431476765894288711928248346 : Int)/10^30)
theorem v3322_mb_checked : Scalar.distance (sourceCoefficient 44 45 3 1) v3322_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3322_mg : Scalar.QComplex := ((-93086266991323299781728 : Int)/10^30,(174151004744460498720 : Int)/10^30)
theorem v3322_mg_checked : Scalar.distance (sourceCoefficient 44 45 3 2) v3322_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3322_upper : Scalar.QComplex := ((999996263146708121576017016392 : Int)/10^30,(-2733805519725995970495800233 : Int)/10^30)
theorem v3322_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 45 5) 1) 14) v3322_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3322 : Material (44 : Basis) (45 : Basis) where
  plus := ![v3322_pa,v3322_pb,v3322_pg]
  minus := ![(Primitive.Addresses.material3322 1).one,v3322_mb,v3322_mg]
  upper := v3322_upper
  lower := (Primitive.Addresses.material3322 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3322_pa_checked.trans (by decide +kernel)
    · exact v3322_pb_checked.trans (by decide +kernel)
    · exact v3322_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 45 Primitive.Addresses.material3322
    · exact v3322_mb_checked.trans (by decide +kernel)
    · exact v3322_mg_checked.trans (by decide +kernel)
  upper_error := v3322_upper_checked
  lower_error := reuse_lower_error 44 45 Primitive.Addresses.material3322

def v3323_pa : Scalar.QComplex := ((999999475442667841975870730740 : Int)/10^30,(-1024262851594088390130397841 : Int)/10^30)
theorem v3323_pa_checked : Scalar.distance (sourceCoefficient 44 46 1 0) v3323_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3323_pb : Scalar.QComplex := ((-441946396031503642944139 : Int)/10^30,(-431477294639230777349520118 : Int)/10^30)
theorem v3323_pb_checked : Scalar.distance (sourceCoefficient 44 46 1 1) v3323_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3323_pg : Scalar.QComplex := ((-93086381064923957877392 : Int)/10^30,(95344972128037181628 : Int)/10^30)
theorem v3323_pg_checked : Scalar.distance (sourceCoefficient 44 46 1 2) v3323_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3323_mb : Scalar.QComplex := ((-814291703732355523879424 : Int)/10^30,(-431476752600679248235338523 : Int)/10^30)
theorem v3323_mb_checked : Scalar.distance (sourceCoefficient 44 46 3 1) v3323_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3323_mg : Scalar.QComplex := ((-93086264126193261268110 : Int)/10^30,(175674291030804033411 : Int)/10^30)
theorem v3323_mg_checked : Scalar.distance (sourceCoefficient 44 46 3 2) v3323_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3323_upper : Scalar.QComplex := ((999996218276155908843632171464 : Int)/10^30,(-2750169701445181685693025744 : Int)/10^30)
theorem v3323_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 46 5) 1) 14) v3323_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3323 : Material (44 : Basis) (46 : Basis) where
  plus := ![v3323_pa,v3323_pb,v3323_pg]
  minus := ![(Primitive.Addresses.material3323 1).one,v3323_mb,v3323_mg]
  upper := v3323_upper
  lower := (Primitive.Addresses.material3323 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3323_pa_checked.trans (by decide +kernel)
    · exact v3323_pb_checked.trans (by decide +kernel)
    · exact v3323_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 46 Primitive.Addresses.material3323
    · exact v3323_mb_checked.trans (by decide +kernel)
    · exact v3323_mg_checked.trans (by decide +kernel)
  upper_error := v3323_upper_checked
  lower_error := reuse_lower_error 44 46 Primitive.Addresses.material3323

def v3324_pa : Scalar.QComplex := ((999999471401322906683541782274 : Int)/10^30,(-1028200892223923083107511947 : Int)/10^30)
theorem v3324_pa_checked : Scalar.distance (sourceCoefficient 44 47 1 0) v3324_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3324_pb : Scalar.QComplex := ((-443645572027586051708178 : Int)/10^30,(-431477292883447385596321568 : Int)/10^30)
theorem v3324_pb_checked : Scalar.distance (sourceCoefficient 44 47 1 1) v3324_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3324_pg : Scalar.QComplex := ((-93086380687431496748149 : Int)/10^30,(95711550269711682624 : Int)/10^30)
theorem v3324_pg_checked : Scalar.distance (sourceCoefficient 44 47 1 2) v3324_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3324_mb : Scalar.QComplex := ((-815990877580595063588126 : Int)/10^30,(-431476749378584153667430172 : Int)/10^30)
theorem v3324_mb_checked : Scalar.distance (sourceCoefficient 44 47 3 1) v3324_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3324_mg : Scalar.QComplex := ((-93086263432360514498088 : Int)/10^30,(176040868710225746488 : Int)/10^30)
theorem v3324_mg_checked : Scalar.distance (sourceCoefficient 44 47 3 2) v3324_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3324_upper : Scalar.QComplex := ((999996207438116121820380426980 : Int)/10^30,(-2754107729234772724913283319 : Int)/10^30)
theorem v3324_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 47 5) 1) 14) v3324_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3324 : Material (44 : Basis) (47 : Basis) where
  plus := ![v3324_pa,v3324_pb,v3324_pg]
  minus := ![(Primitive.Addresses.material3324 1).one,v3324_mb,v3324_mg]
  upper := v3324_upper
  lower := (Primitive.Addresses.material3324 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3324_pa_checked.trans (by decide +kernel)
    · exact v3324_pb_checked.trans (by decide +kernel)
    · exact v3324_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 47 Primitive.Addresses.material3324
    · exact v3324_mb_checked.trans (by decide +kernel)
    · exact v3324_mg_checked.trans (by decide +kernel)
  upper_error := v3324_upper_checked
  lower_error := reuse_lower_error 44 47 Primitive.Addresses.material3324

def v3325_pa : Scalar.QComplex := ((999999442820970773559411793136 : Int)/10^30,(-1055631445157073069034203327 : Int)/10^30)
theorem v3325_pa_checked : Scalar.distance (sourceCoefficient 44 48 1 0) v3325_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3325_pb : Scalar.QComplex := ((-455481238851989417916582 : Int)/10^30,(-431477280405967314526810545 : Int)/10^30)
theorem v3325_pb_checked : Scalar.distance (sourceCoefficient 44 48 1 1) v3325_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3325_pg : Scalar.QComplex := ((-93086378011271919263845 : Int)/10^30,(98264962495652975800 : Int)/10^30)
theorem v3325_pg_checked : Scalar.distance (sourceCoefficient 44 48 1 2) v3325_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3325_mb : Scalar.QComplex := ((-827826529230535417883752 : Int)/10^30,(-431476726687461317719597635 : Int)/10^30)
theorem v3325_mb_checked : Scalar.distance (sourceCoefficient 44 48 3 1) v3325_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3325_mg : Scalar.QComplex := ((-93086258552722183900568 : Int)/10^30,(178594277676009785626 : Int)/10^30)
theorem v3325_mg_checked : Scalar.distance (sourceCoefficient 44 48 3 2) v3325_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3325_upper : Scalar.QComplex := ((999996131515160673479746878951 : Int)/10^30,(-2781538191986241343528654778 : Int)/10^30)
theorem v3325_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 48 5) 1) 14) v3325_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3325 : Material (44 : Basis) (48 : Basis) where
  plus := ![v3325_pa,v3325_pb,v3325_pg]
  minus := ![(Primitive.Addresses.material3325 1).one,v3325_mb,v3325_mg]
  upper := v3325_upper
  lower := (Primitive.Addresses.material3325 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3325_pa_checked.trans (by decide +kernel)
    · exact v3325_pb_checked.trans (by decide +kernel)
    · exact v3325_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 48 Primitive.Addresses.material3325
    · exact v3325_mb_checked.trans (by decide +kernel)
    · exact v3325_mg_checked.trans (by decide +kernel)
  upper_error := v3325_upper_checked
  lower_error := reuse_lower_error 44 48 Primitive.Addresses.material3325

def v3326_pa : Scalar.QComplex := ((999999419313714504581489681473 : Int)/10^30,(-1077669816685182501994137871 : Int)/10^30)
theorem v3326_pa_checked : Scalar.distance (sourceCoefficient 44 49 1 0) v3326_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3326_pb : Scalar.QComplex := ((-464990300551122863914600 : Int)/10^30,(-431477270067654720345488267 : Int)/10^30)
theorem v3326_pb_checked : Scalar.distance (sourceCoefficient 44 49 1 1) v3326_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3326_pg : Scalar.QComplex := ((-93086375801981213809916 : Int)/10^30,(100316435798787581133 : Int)/10^30)
theorem v3326_pg_checked : Scalar.distance (sourceCoefficient 44 49 1 2) v3326_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3326_mb : Scalar.QComplex := ((-837335578467512459241897 : Int)/10^30,(-431476708143260598853090593 : Int)/10^30)
theorem v3326_mb_checked : Scalar.distance (sourceCoefficient 44 49 3 1) v3326_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3326_mg : Scalar.QComplex := ((-93086254573103235389086 : Int)/10^30,(180645748308768747193 : Int)/10^30)
theorem v3326_mg_checked : Scalar.distance (sourceCoefficient 44 49 3 2) v3326_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3326_upper : Scalar.QComplex := ((999996069971709463729112833539 : Int)/10^30,(-2803576490119393435717363334 : Int)/10^30)
theorem v3326_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 49 5) 1) 14) v3326_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3326 : Material (44 : Basis) (49 : Basis) where
  plus := ![v3326_pa,v3326_pb,v3326_pg]
  minus := ![(Primitive.Addresses.material3326 1).one,v3326_mb,v3326_mg]
  upper := v3326_upper
  lower := (Primitive.Addresses.material3326 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3326_pa_checked.trans (by decide +kernel)
    · exact v3326_pb_checked.trans (by decide +kernel)
    · exact v3326_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 49 Primitive.Addresses.material3326
    · exact v3326_mb_checked.trans (by decide +kernel)
    · exact v3326_mg_checked.trans (by decide +kernel)
  upper_error := v3326_upper_checked
  lower_error := reuse_lower_error 44 49 Primitive.Addresses.material3326

def v3327_pa : Scalar.QComplex := ((999999416535095758940136572742 : Int)/10^30,(-1080245096286405387089733479 : Int)/10^30)
theorem v3327_pa_checked : Scalar.distance (sourceCoefficient 44 50 1 0) v3327_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3327_pb : Scalar.QComplex := ((-466101475778766343657587 : Int)/10^30,(-431477268841344499452439803 : Int)/10^30)
theorem v3327_pb_checked : Scalar.distance (sourceCoefficient 44 50 1 1) v3327_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3327_pg : Scalar.QComplex := ((-93086375540374034619633 : Int)/10^30,(100556159379553743563 : Int)/10^30)
theorem v3327_pg_checked : Scalar.distance (sourceCoefficient 44 50 1 2) v3327_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3327_mb : Scalar.QComplex := ((-838446752223164128847950 : Int)/10^30,(-431476705958056658589537220 : Int)/10^30)
theorem v3327_mb_checked : Scalar.distance (sourceCoefficient 44 50 3 1) v3327_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3327_mg : Scalar.QComplex := ((-93086254104625500155197 : Int)/10^30,(180885471574519651304 : Int)/10^30)
theorem v3327_mg_checked : Scalar.distance (sourceCoefficient 44 50 3 2) v3327_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3327_upper : Scalar.QComplex := ((999996062748395892343706943730 : Int)/10^30,(-2806151761089395987730384631 : Int)/10^30)
theorem v3327_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 50 5) 1) 14) v3327_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3327 : Material (44 : Basis) (50 : Basis) where
  plus := ![v3327_pa,v3327_pb,v3327_pg]
  minus := ![(Primitive.Addresses.material3327 1).one,v3327_mb,v3327_mg]
  upper := v3327_upper
  lower := (Primitive.Addresses.material3327 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3327_pa_checked.trans (by decide +kernel)
    · exact v3327_pb_checked.trans (by decide +kernel)
    · exact v3327_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 50 Primitive.Addresses.material3327
    · exact v3327_mb_checked.trans (by decide +kernel)
    · exact v3327_mg_checked.trans (by decide +kernel)
  upper_error := v3327_upper_checked
  lower_error := reuse_lower_error 44 50 Primitive.Addresses.material3327

def v3328_pa : Scalar.QComplex := ((999999404265299308921876498976 : Int)/10^30,(-1091544340135719195564327801 : Int)/10^30)
theorem v3328_pa_checked : Scalar.distance (sourceCoefficient 44 51 1 0) v3328_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3328_pb : Scalar.QComplex := ((-470976845355922841621909 : Int)/10^30,(-431477263415715291957767455 : Int)/10^30)
theorem v3328_pb_checked : Scalar.distance (sourceCoefficient 44 51 1 1) v3328_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3328_pg : Scalar.QComplex := ((-93086374384038973881674 : Int)/10^30,(101607965634043330956 : Int)/10^30)
theorem v3328_pg_checked : Scalar.distance (sourceCoefficient 44 51 1 2) v3328_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3328_mb : Scalar.QComplex := ((-843322115302924073040414 : Int)/10^30,(-431476696325205104713142844 : Int)/10^30)
theorem v3328_mb_checked : Scalar.distance (sourceCoefficient 44 51 3 1) v3328_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3328_mg : Scalar.QComplex := ((-93086252040629443944300 : Int)/10^30,(181937276439508622210 : Int)/10^30)
theorem v3328_mg_checked : Scalar.distance (sourceCoefficient 44 51 3 2) v3328_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3328_upper : Scalar.QComplex := ((999996030977147892224999393895 : Int)/10^30,(-2817450966933257819579823526 : Int)/10^30)
theorem v3328_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 51 5) 1) 14) v3328_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3328 : Material (44 : Basis) (51 : Basis) where
  plus := ![v3328_pa,v3328_pb,v3328_pg]
  minus := ![(Primitive.Addresses.material3328 1).one,v3328_mb,v3328_mg]
  upper := v3328_upper
  lower := (Primitive.Addresses.material3328 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3328_pa_checked.trans (by decide +kernel)
    · exact v3328_pb_checked.trans (by decide +kernel)
    · exact v3328_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 51 Primitive.Addresses.material3328
    · exact v3328_mb_checked.trans (by decide +kernel)
    · exact v3328_mg_checked.trans (by decide +kernel)
  upper_error := v3328_upper_checked
  lower_error := reuse_lower_error 44 51 Primitive.Addresses.material3328

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
