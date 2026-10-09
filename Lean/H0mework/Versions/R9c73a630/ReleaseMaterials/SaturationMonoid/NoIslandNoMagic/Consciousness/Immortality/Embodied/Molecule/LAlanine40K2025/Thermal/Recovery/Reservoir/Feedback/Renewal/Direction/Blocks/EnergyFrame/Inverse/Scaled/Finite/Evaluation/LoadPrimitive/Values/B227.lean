import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B151
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B152

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3633_pa : Scalar.QComplex := ((999999217126903799544179275774 : Int)/10^30,(-1251297558341191236802480135 : Int)/10^30)
theorem v3633_pa_checked : Scalar.distance (sourceCoefficient 50 59 1 0) v3633_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3633_pb : Scalar.QComplex := ((-539906767681506986542006 : Int)/10^30,(-431477182548619565494766039 : Int)/10^30)
theorem v3633_pb_checked : Scalar.distance (sourceCoefficient 50 59 1 1) v3633_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3633_pg : Scalar.QComplex := ((-93086356950932502046945 : Int)/10^30,(116478822355714714293 : Int)/10^30)
theorem v3633_pg_checked : Scalar.distance (sourceCoefficient 50 59 1 2) v3633_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3633_mb : Scalar.QComplex := ((-912251942178086389921740 : Int)/10^30,(-431476555974721010244087850 : Int)/10^30)
theorem v3633_mb_checked : Scalar.distance (sourceCoefficient 50 59 3 1) v3633_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3633_mg : Scalar.QComplex := ((-93086221774649870973578 : Int)/10^30,(196808112580094689119 : Int)/10^30)
theorem v3633_mg_checked : Scalar.distance (sourceCoefficient 50 59 3 2) v3633_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3633_upper : Scalar.QComplex := ((999995568119469179604700718922 : Int)/10^30,(-2977203624221183688449726637 : Int)/10^30)
theorem v3633_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 59 5) 1) 14) v3633_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3633 : Material (50 : Basis) (59 : Basis) where
  plus := ![v3633_pa,v3633_pb,v3633_pg]
  minus := ![(Primitive.Addresses.material3633 1).one,v3633_mb,v3633_mg]
  upper := v3633_upper
  lower := (Primitive.Addresses.material3633 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3633_pa_checked.trans (by decide +kernel)
    · exact v3633_pb_checked.trans (by decide +kernel)
    · exact v3633_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 59 Primitive.Addresses.material3633
    · exact v3633_mb_checked.trans (by decide +kernel)
    · exact v3633_mg_checked.trans (by decide +kernel)
  upper_error := v3633_upper_checked
  lower_error := reuse_lower_error 50 59 Primitive.Addresses.material3633

def v3634_pa : Scalar.QComplex := ((999999191565384146707835494522 : Int)/10^30,(-1271561472418874532782096052 : Int)/10^30)
theorem v3634_pa_checked : Scalar.distance (sourceCoefficient 50 60 1 0) v3634_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3634_pb : Scalar.QComplex := ((-548650190687593821280184 : Int)/10^30,(-431477171210683612488979016 : Int)/10^30)
theorem v3634_pb_checked : Scalar.distance (sourceCoefficient 50 60 1 1) v3634_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3634_pg : Scalar.QComplex := ((-93086354538201017242517 : Int)/10^30,(118365117729158750785 : Int)/10^30)
theorem v3634_pg_checked : Scalar.distance (sourceCoefficient 50 60 1 2) v3634_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3634_mb : Scalar.QComplex := ((-920995352144469159557478 : Int)/10^30,(-431476537091609013771140643 : Int)/10^30)
theorem v3634_mb_checked : Scalar.distance (sourceCoefficient 50 60 3 1) v3634_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3634_mg : Scalar.QComplex := ((-93086217734131332847066 : Int)/10^30,(198694405169106144126 : Int)/10^30)
theorem v3634_mg_checked : Scalar.distance (sourceCoefficient 50 60 3 2) v3634_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3634_upper : Scalar.QComplex := ((999995507584310227492741697923 : Int)/10^30,(-2997467464001283334432212649 : Int)/10^30)
theorem v3634_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 60 5) 1) 14) v3634_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3634 : Material (50 : Basis) (60 : Basis) where
  plus := ![v3634_pa,v3634_pb,v3634_pg]
  minus := ![(Primitive.Addresses.material3634 1).one,v3634_mb,v3634_mg]
  upper := v3634_upper
  lower := (Primitive.Addresses.material3634 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3634_pa_checked.trans (by decide +kernel)
    · exact v3634_pb_checked.trans (by decide +kernel)
    · exact v3634_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 60 Primitive.Addresses.material3634
    · exact v3634_mb_checked.trans (by decide +kernel)
    · exact v3634_mg_checked.trans (by decide +kernel)
  upper_error := v3634_upper_checked
  lower_error := reuse_lower_error 50 60 Primitive.Addresses.material3634

def v3635_pa : Scalar.QComplex := ((999999184097712868457357741860 : Int)/10^30,(-1277420803246347298985288999 : Int)/10^30)
theorem v3635_pa_checked : Scalar.distance (sourceCoefficient 50 61 1 0) v3635_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3635_pb : Scalar.QComplex := ((-551178360093988754511355 : Int)/10^30,(-431477167888278786336500257 : Int)/10^30)
theorem v3635_pb_checked : Scalar.distance (sourceCoefficient 50 61 1 1) v3635_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3635_pg : Scalar.QComplex := ((-93086353832245821652187 : Int)/10^30,(118910541903044259372 : Int)/10^30)
theorem v3635_pg_checked : Scalar.distance (sourceCoefficient 50 61 1 2) v3635_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3635_mb : Scalar.QComplex := ((-923523517742425350327048 : Int)/10^30,(-431476531587509091506206926 : Int)/10^30)
theorem v3635_mb_checked : Scalar.distance (sourceCoefficient 50 61 3 1) v3635_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3635_mg : Scalar.QComplex := ((-93086216557499903045822 : Int)/10^30,(199239828530697766907 : Int)/10^30)
theorem v3635_mg_checked : Scalar.distance (sourceCoefficient 50 61 3 2) v3635_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3635_upper : Scalar.QComplex := ((999995490003976617583817835697 : Int)/10^30,(-3003326773213447954049120721 : Int)/10^30)
theorem v3635_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 61 5) 1) 14) v3635_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3635 : Material (50 : Basis) (61 : Basis) where
  plus := ![v3635_pa,v3635_pb,v3635_pg]
  minus := ![(Primitive.Addresses.material3635 1).one,v3635_mb,v3635_mg]
  upper := v3635_upper
  lower := (Primitive.Addresses.material3635 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3635_pa_checked.trans (by decide +kernel)
    · exact v3635_pb_checked.trans (by decide +kernel)
    · exact v3635_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 61 Primitive.Addresses.material3635
    · exact v3635_mb_checked.trans (by decide +kernel)
    · exact v3635_mg_checked.trans (by decide +kernel)
  upper_error := v3635_upper_checked
  lower_error := reuse_lower_error 50 61 Primitive.Addresses.material3635

def v3636_pa : Scalar.QComplex := ((999999173186326909211083564253 : Int)/10^30,(-1285934159496794696991451872 : Int)/10^30)
theorem v3636_pa_checked : Scalar.distance (sourceCoefficient 50 62 1 0) v3636_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3636_pb : Scalar.QComplex := ((-554851681736562099559127 : Int)/10^30,(-431477163025770074350048805 : Int)/10^30)
theorem v3636_pb_checked : Scalar.distance (sourceCoefficient 50 62 1 1) v3636_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3636_pg : Scalar.QComplex := ((-93086352799879014075697 : Int)/10^30,(119703019820428019488 : Int)/10^30)
theorem v3636_pg_checked : Scalar.distance (sourceCoefficient 50 62 1 2) v3636_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3636_mb : Scalar.QComplex := ((-927196833821127149570748 : Int)/10^30,(-431476523555091052778529969 : Int)/10^30)
theorem v3636_mb_checked : Scalar.distance (sourceCoefficient 50 62 3 1) v3636_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3636_mg : Scalar.QComplex := ((-93086214841260729044945 : Int)/10^30,(200032305262119721487 : Int)/10^30)
theorem v3636_mg_checked : Scalar.distance (sourceCoefficient 50 62 3 2) v3636_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3636_upper : Scalar.QComplex := ((999995464399326346938943291810 : Int)/10^30,(-3011840097952188973631366286 : Int)/10^30)
theorem v3636_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 62 5) 1) 14) v3636_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3636 : Material (50 : Basis) (62 : Basis) where
  plus := ![v3636_pa,v3636_pb,v3636_pg]
  minus := ![(Primitive.Addresses.material3636 1).one,v3636_mb,v3636_mg]
  upper := v3636_upper
  lower := (Primitive.Addresses.material3636 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3636_pa_checked.trans (by decide +kernel)
    · exact v3636_pb_checked.trans (by decide +kernel)
    · exact v3636_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 62 Primitive.Addresses.material3636
    · exact v3636_mb_checked.trans (by decide +kernel)
    · exact v3636_mg_checked.trans (by decide +kernel)
  upper_error := v3636_upper_checked
  lower_error := reuse_lower_error 50 62 Primitive.Addresses.material3636

def v3637_pa : Scalar.QComplex := ((999999140993965829106871118315 : Int)/10^30,(-1310729312425116826706409749 : Int)/10^30)
theorem v3637_pa_checked : Scalar.distance (sourceCoefficient 50 63 1 0) v3637_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3637_pb : Scalar.QComplex := ((-565550232156956160849498 : Int)/10^30,(-431477148626142813425077416 : Int)/10^30)
theorem v3637_pb_checked : Scalar.distance (sourceCoefficient 50 63 1 1) v3637_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3637_pg : Scalar.QComplex := ((-93086349748264092334942 : Int)/10^30,(122011112009987593035 : Int)/10^30)
theorem v3637_pg_checked : Scalar.distance (sourceCoefficient 50 63 1 2) v3637_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3637_mb : Scalar.QComplex := ((-937895367831732150398507 : Int)/10^30,(-431476499923101985516822305 : Int)/10^30)
theorem v3637_mb_checked : Scalar.distance (sourceCoefficient 50 63 3 1) v3637_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3637_mg : Scalar.QComplex := ((-93086209797867336583294 : Int)/10^30,(202340393958864850009 : Int)/10^30)
theorem v3637_mg_checked : Scalar.distance (sourceCoefficient 50 63 3 2) v3637_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3637_upper : Scalar.QComplex := ((999995389412828657993302406951 : Int)/10^30,(-3036635158389948703799373622 : Int)/10^30)
theorem v3637_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 63 5) 1) 14) v3637_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3637 : Material (50 : Basis) (63 : Basis) where
  plus := ![v3637_pa,v3637_pb,v3637_pg]
  minus := ![(Primitive.Addresses.material3637 1).one,v3637_mb,v3637_mg]
  upper := v3637_upper
  lower := (Primitive.Addresses.material3637 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3637_pa_checked.trans (by decide +kernel)
    · exact v3637_pb_checked.trans (by decide +kernel)
    · exact v3637_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 63 Primitive.Addresses.material3637
    · exact v3637_mb_checked.trans (by decide +kernel)
    · exact v3637_mg_checked.trans (by decide +kernel)
  upper_error := v3637_upper_checked
  lower_error := reuse_lower_error 50 63 Primitive.Addresses.material3637

def v3638_pa : Scalar.QComplex := ((999999093917395824260418348402 : Int)/10^30,(-1346166552609963479853705414 : Int)/10^30)
theorem v3638_pa_checked : Scalar.distance (sourceCoefficient 50 64 1 0) v3638_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3638_pb : Scalar.QComplex := ((-580840603455029236976081 : Int)/10^30,(-431477127432205994455045565 : Int)/10^30)
theorem v3638_pb_checked : Scalar.distance (sourceCoefficient 50 64 1 1) v3638_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3638_pg : Scalar.QComplex := ((-93086345270992240221688 : Int)/10^30,(125309838049576789527 : Int)/10^30)
theorem v3638_pg_checked : Scalar.distance (sourceCoefficient 50 64 1 2) v3638_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3638_mb : Scalar.QComplex := ((-953185715147088252471538 : Int)/10^30,(-431476465534271280540287363 : Int)/10^30)
theorem v3638_mb_checked : Scalar.distance (sourceCoefficient 50 64 3 1) v3638_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3638_mg : Scalar.QComplex := ((-93086202473945148503174 : Int)/10^30,(205639114906503623199 : Int)/10^30)
theorem v3638_mg_checked : Scalar.distance (sourceCoefficient 50 64 3 2) v3638_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3638_upper : Scalar.QComplex := ((999995281174867050439153231352 : Int)/10^30,(-3072072264545299776971545784 : Int)/10^30)
theorem v3638_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 64 5) 1) 14) v3638_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3638 : Material (50 : Basis) (64 : Basis) where
  plus := ![v3638_pa,v3638_pb,v3638_pg]
  minus := ![(Primitive.Addresses.material3638 1).one,v3638_mb,v3638_mg]
  upper := v3638_upper
  lower := (Primitive.Addresses.material3638 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3638_pa_checked.trans (by decide +kernel)
    · exact v3638_pb_checked.trans (by decide +kernel)
    · exact v3638_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 64 Primitive.Addresses.material3638
    · exact v3638_mb_checked.trans (by decide +kernel)
    · exact v3638_mg_checked.trans (by decide +kernel)
  upper_error := v3638_upper_checked
  lower_error := reuse_lower_error 50 64 Primitive.Addresses.material3638

def v3639_pa : Scalar.QComplex := ((999999044853538244100523948063 : Int)/10^30,(-1382133138017837826882931796 : Int)/10^30)
theorem v3639_pa_checked : Scalar.distance (sourceCoefficient 50 65 1 0) v3639_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3639_pb : Scalar.QComplex := ((-596359374979909031301779 : Int)/10^30,(-431477105182949075905725739 : Int)/10^30)
theorem v3639_pb_checked : Scalar.distance (sourceCoefficient 50 65 1 1) v3639_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3639_pg : Scalar.QComplex := ((-93086340587388905044933 : Int)/10^30,(128657838909724660369 : Int)/10^30)
theorem v3639_pg_checked : Scalar.distance (sourceCoefficient 50 65 1 2) v3639_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3639_mb : Scalar.QComplex := ((-968704461693513513813478 : Int)/10^30,(-431476429893021759958522957 : Int)/10^30)
theorem v3639_mb_checked : Scalar.distance (sourceCoefficient 50 65 3 1) v3639_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3639_mg : Scalar.QComplex := ((-93086194901169603299593 : Int)/10^30,(208987110478299026016 : Int)/10^30)
theorem v3639_mg_checked : Scalar.distance (sourceCoefficient 50 65 3 2) v3639_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3639_upper : Scalar.QComplex := ((999995170036018994280670190856 : Int)/10^30,(-3108038711705402945913311131 : Int)/10^30)
theorem v3639_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 65 5) 1) 14) v3639_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3639 : Material (50 : Basis) (65 : Basis) where
  plus := ![v3639_pa,v3639_pb,v3639_pg]
  minus := ![(Primitive.Addresses.material3639 1).one,v3639_mb,v3639_mg]
  upper := v3639_upper
  lower := (Primitive.Addresses.material3639 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3639_pa_checked.trans (by decide +kernel)
    · exact v3639_pb_checked.trans (by decide +kernel)
    · exact v3639_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 65 Primitive.Addresses.material3639
    · exact v3639_mb_checked.trans (by decide +kernel)
    · exact v3639_mg_checked.trans (by decide +kernel)
  upper_error := v3639_upper_checked
  lower_error := reuse_lower_error 50 65 Primitive.Addresses.material3639

def v3640_pa : Scalar.QComplex := ((999999020390518640776942629389 : Int)/10^30,(-1399720687524375395110619590 : Int)/10^30)
theorem v3640_pa_checked : Scalar.distance (sourceCoefficient 50 66 1 0) v3640_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3640_pb : Scalar.QComplex := ((-603948006342957167324858 : Int)/10^30,(-431477094032195249036506829 : Int)/10^30)
theorem v3640_pb_checked : Scalar.distance (sourceCoefficient 50 66 1 1) v3640_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3640_pg : Scalar.QComplex := ((-93086338245976365227630 : Int)/10^30,(130295001007002958489 : Int)/10^30)
theorem v3640_pg_checked : Scalar.distance (sourceCoefficient 50 66 1 2) v3640_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3640_mb : Scalar.QComplex := ((-976293080608369034508574 : Int)/10^30,(-431476412193624997983175867 : Int)/10^30)
theorem v3640_mb_checked : Scalar.distance (sourceCoefficient 50 66 3 1) v3640_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3640_mg : Scalar.QComplex := ((-93086191146960780389704 : Int)/10^30,(210624269945453484759 : Int)/10^30)
theorem v3640_mg_checked : Scalar.distance (sourceCoefficient 50 66 3 2) v3640_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3640_upper : Scalar.QComplex := ((999995115218520907494953612116 : Int)/10^30,(-3125626192796398935311360084 : Int)/10^30)
theorem v3640_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 66 5) 1) 14) v3640_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3640 : Material (50 : Basis) (66 : Basis) where
  plus := ![v3640_pa,v3640_pb,v3640_pg]
  minus := ![(Primitive.Addresses.material3640 1).one,v3640_mb,v3640_mg]
  upper := v3640_upper
  lower := (Primitive.Addresses.material3640 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3640_pa_checked.trans (by decide +kernel)
    · exact v3640_pb_checked.trans (by decide +kernel)
    · exact v3640_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 66 Primitive.Addresses.material3640
    · exact v3640_mb_checked.trans (by decide +kernel)
    · exact v3640_mg_checked.trans (by decide +kernel)
  upper_error := v3640_upper_checked
  lower_error := reuse_lower_error 50 66 Primitive.Addresses.material3640

def v3641_pa : Scalar.QComplex := ((999998978639115366879827823866 : Int)/10^30,(-1429237812992709651603095745 : Int)/10^30)
theorem v3641_pa_checked : Scalar.distance (sourceCoefficient 50 67 1 0) v3641_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3641_pb : Scalar.QComplex := ((-616683980769150167022942 : Int)/10^30,(-431477074917972134404401617 : Int)/10^30)
theorem v3641_pb_checked : Scalar.distance (sourceCoefficient 50 67 1 1) v3641_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3641_pg : Scalar.QComplex := ((-93086334240892331784249 : Int)/10^30,(133042644654514577905 : Int)/10^30)
theorem v3641_pg_checked : Scalar.distance (sourceCoefficient 50 67 1 2) v3641_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3641_mb : Scalar.QComplex := ((-989029033797663017273724 : Int)/10^30,(-431476382088836677640203828 : Int)/10^30)
theorem v3641_mb_checked : Scalar.distance (sourceCoefficient 50 67 3 1) v3641_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3641_mg : Scalar.QComplex := ((-93086184770785519695717 : Int)/10^30,(213371909113684662115 : Int)/10^30)
theorem v3641_mg_checked : Scalar.distance (sourceCoefficient 50 67 3 2) v3641_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3641_upper : Scalar.QComplex := ((999995022523299031768499060135 : Int)/10^30,(-3155143202243307738814806637 : Int)/10^30)
theorem v3641_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 67 5) 1) 14) v3641_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3641 : Material (50 : Basis) (67 : Basis) where
  plus := ![v3641_pa,v3641_pb,v3641_pg]
  minus := ![(Primitive.Addresses.material3641 1).one,v3641_mb,v3641_mg]
  upper := v3641_upper
  lower := (Primitive.Addresses.material3641 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3641_pa_checked.trans (by decide +kernel)
    · exact v3641_pb_checked.trans (by decide +kernel)
    · exact v3641_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 67 Primitive.Addresses.material3641
    · exact v3641_mb_checked.trans (by decide +kernel)
    · exact v3641_mg_checked.trans (by decide +kernel)
  upper_error := v3641_upper_checked
  lower_error := reuse_lower_error 50 67 Primitive.Addresses.material3641

def v3642_pa : Scalar.QComplex := ((999998907172414771288832206195 : Int)/10^30,(-1478395744104159445808303500 : Int)/10^30)
theorem v3642_pa_checked : Scalar.distance (sourceCoefficient 50 68 1 0) v3642_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3642_pb : Scalar.QComplex := ((-637894519639637160422308 : Int)/10^30,(-431477041972577014154397868 : Int)/10^30)
theorem v3642_pb_checked : Scalar.distance (sourceCoefficient 50 68 1 1) v3642_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3642_pg : Scalar.QComplex := ((-93086327360802806619401 : Int)/10^30,(137618580597878559382 : Int)/10^30)
theorem v3642_pg_checked : Scalar.distance (sourceCoefficient 50 68 1 2) v3642_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3642_mb : Scalar.QComplex := ((-1010239536340104836415588 : Int)/10^30,(-431476330839714066445005624 : Int)/10^30)
theorem v3642_mb_checked : Scalar.distance (sourceCoefficient 50 68 3 1) v3642_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3642_mg : Scalar.QComplex := ((-93086173941871929683895 : Int)/10^30,(217947837416011168786 : Int)/10^30)
theorem v3642_mg_checked : Scalar.distance (sourceCoefficient 50 68 3 2) v3642_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3642_upper : Scalar.QComplex := ((999994866214575351744788156955 : Int)/10^30,(-3204300936794751819182498844 : Int)/10^30)
theorem v3642_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 68 5) 1) 14) v3642_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3642 : Material (50 : Basis) (68 : Basis) where
  plus := ![v3642_pa,v3642_pb,v3642_pg]
  minus := ![(Primitive.Addresses.material3642 1).one,v3642_mb,v3642_mg]
  upper := v3642_upper
  lower := (Primitive.Addresses.material3642 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3642_pa_checked.trans (by decide +kernel)
    · exact v3642_pb_checked.trans (by decide +kernel)
    · exact v3642_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 68 Primitive.Addresses.material3642
    · exact v3642_mb_checked.trans (by decide +kernel)
    · exact v3642_mg_checked.trans (by decide +kernel)
  upper_error := v3642_upper_checked
  lower_error := reuse_lower_error 50 68 Primitive.Addresses.material3642

def v3643_pa : Scalar.QComplex := ((999998874952704828855747005694 : Int)/10^30,(-1500031107881057290068774152 : Int)/10^30)
theorem v3643_pa_checked : Scalar.distance (sourceCoefficient 50 69 1 0) v3643_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3643_pb : Scalar.QComplex := ((-647229691048179341384708 : Int)/10^30,(-431477027032086803924768279 : Int)/10^30)
theorem v3643_pb_checked : Scalar.distance (sourceCoefficient 50 69 1 1) v3643_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3643_pg : Scalar.QComplex := ((-93086324249572427196107 : Int)/10^30,(139632539185871985774 : Int)/10^30)
theorem v3643_pg_checked : Scalar.distance (sourceCoefficient 50 69 1 2) v3643_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3643_mb : Scalar.QComplex := ((-1019574691379765906839872 : Int)/10^30,(-431476307843396934183548538 : Int)/10^30)
theorem v3643_mb_checked : Scalar.distance (sourceCoefficient 50 69 3 1) v3643_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3643_mg : Scalar.QComplex := ((-93086169092687152603197 : Int)/10^30,(219961792569264077586 : Int)/10^30)
theorem v3643_mg_checked : Scalar.distance (sourceCoefficient 50 69 3 2) v3643_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3643_upper : Scalar.QComplex := ((999994796654238262728908672269 : Int)/10^30,(-3225936212740020374724925748 : Int)/10^30)
theorem v3643_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 69 5) 1) 14) v3643_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3643 : Material (50 : Basis) (69 : Basis) where
  plus := ![v3643_pa,v3643_pb,v3643_pg]
  minus := ![(Primitive.Addresses.material3643 1).one,v3643_mb,v3643_mg]
  upper := v3643_upper
  lower := (Primitive.Addresses.material3643 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3643_pa_checked.trans (by decide +kernel)
    · exact v3643_pb_checked.trans (by decide +kernel)
    · exact v3643_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 69 Primitive.Addresses.material3643
    · exact v3643_mb_checked.trans (by decide +kernel)
    · exact v3643_mg_checked.trans (by decide +kernel)
  upper_error := v3643_upper_checked
  lower_error := reuse_lower_error 50 69 Primitive.Addresses.material3643

def v3644_pa : Scalar.QComplex := ((999998853503038540004239663147 : Int)/10^30,(-1514263057881525710328946731 : Int)/10^30)
theorem v3644_pa_checked : Scalar.distance (sourceCoefficient 50 70 1 0) v3644_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3644_pb : Scalar.QComplex := ((-653370456341958543798029 : Int)/10^30,(-431477017057253319797348220 : Int)/10^30)
theorem v3644_pb_checked : Scalar.distance (sourceCoefficient 50 70 1 1) v3644_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3644_pg : Scalar.QComplex := ((-93086322175256842832418 : Int)/10^30,(140957340471211848592 : Int)/10^30)
theorem v3644_pg_checked : Scalar.distance (sourceCoefficient 50 70 1 2) v3644_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3644_mb : Scalar.QComplex := ((-1025715445779225496562258 : Int)/10^30,(-431476292569363285413133517 : Int)/10^30)
theorem v3644_mb_checked : Scalar.distance (sourceCoefficient 50 70 3 1) v3644_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3644_mg : Scalar.QComplex := ((-93086165875128498188654 : Int)/10^30,(221286591571278949862 : Int)/10^30)
theorem v3644_mg_checked : Scalar.distance (sourceCoefficient 50 70 3 2) v3644_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3644_upper : Scalar.QComplex := ((999994750641549332245616171364 : Int)/10^30,(-3240168104523492955539644484 : Int)/10^30)
theorem v3644_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 70 5) 1) 14) v3644_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3644 : Material (50 : Basis) (70 : Basis) where
  plus := ![v3644_pa,v3644_pb,v3644_pg]
  minus := ![(Primitive.Addresses.material3644 1).one,v3644_mb,v3644_mg]
  upper := v3644_upper
  lower := (Primitive.Addresses.material3644 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3644_pa_checked.trans (by decide +kernel)
    · exact v3644_pb_checked.trans (by decide +kernel)
    · exact v3644_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 70 Primitive.Addresses.material3644
    · exact v3644_mb_checked.trans (by decide +kernel)
    · exact v3644_mg_checked.trans (by decide +kernel)
  upper_error := v3644_upper_checked
  lower_error := reuse_lower_error 50 70 Primitive.Addresses.material3644

def v3645_pa : Scalar.QComplex := ((999998816422253805980065485102 : Int)/10^30,(-1538555846088064033558054873 : Int)/10^30)
theorem v3645_pa_checked : Scalar.distance (sourceCoefficient 50 71 1 0) v3645_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3645_pb : Scalar.QComplex := ((-663852246156820331291699 : Int)/10^30,(-431476999761812620078274719 : Int)/10^30)
theorem v3645_pb_checked : Scalar.distance (sourceCoefficient 50 71 1 1) v3645_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3645_pg : Scalar.QComplex := ((-93086318583749352892224 : Int)/10^30,(143218669158273219431 : Int)/10^30)
theorem v3645_pg_checked : Scalar.distance (sourceCoefficient 50 71 1 2) v3645_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3645_mb : Scalar.QComplex := ((-1036197216766051528398503 : Int)/10^30,(-431476266228616497640093672 : Int)/10^30)
theorem v3645_mb_checked : Scalar.distance (sourceCoefficient 50 71 3 1) v3645_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3645_mg : Scalar.QComplex := ((-93086160332197535060223 : Int)/10^30,(223547916317035094356 : Int)/10^30)
theorem v3645_mg_checked : Scalar.distance (sourceCoefficient 50 71 3 2) v3645_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3645_upper : Scalar.QComplex := ((999994671633671205740107146816 : Int)/10^30,(-3264460792550706368076999166 : Int)/10^30)
theorem v3645_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 71 5) 1) 14) v3645_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3645 : Material (50 : Basis) (71 : Basis) where
  plus := ![v3645_pa,v3645_pb,v3645_pg]
  minus := ![(Primitive.Addresses.material3645 1).one,v3645_mb,v3645_mg]
  upper := v3645_upper
  lower := (Primitive.Addresses.material3645 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3645_pa_checked.trans (by decide +kernel)
    · exact v3645_pb_checked.trans (by decide +kernel)
    · exact v3645_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 71 Primitive.Addresses.material3645
    · exact v3645_mb_checked.trans (by decide +kernel)
    · exact v3645_mg_checked.trans (by decide +kernel)
  upper_error := v3645_upper_checked
  lower_error := reuse_lower_error 50 71 Primitive.Addresses.material3645

def v3646_pa : Scalar.QComplex := ((999998775514387576920779291494 : Int)/10^30,(-1564918440520509493779976173 : Int)/10^30)
theorem v3646_pa_checked : Scalar.distance (sourceCoefficient 50 72 1 0) v3646_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3646_pb : Scalar.QComplex := ((-675227110420427735434657 : Int)/10^30,(-431476980608623950304245179 : Int)/10^30)
theorem v3646_pb_checked : Scalar.distance (sourceCoefficient 50 72 1 1) v3646_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3646_pg : Scalar.QComplex := ((-93086314613723054785384 : Int)/10^30,(145672668673195909587 : Int)/10^30)
theorem v3646_pg_checked : Scalar.distance (sourceCoefficient 50 72 1 2) v3646_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3646_mb : Scalar.QComplex := ((-1047572060265937915802579 : Int)/10^30,(-431476237259439404849142294 : Int)/10^30)
theorem v3646_mb_checked : Scalar.distance (sourceCoefficient 50 72 3 1) v3646_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3646_mg : Scalar.QComplex := ((-93086154244481657832638 : Int)/10^30,(226001911492267719869 : Int)/10^30)
theorem v3646_mg_checked : Scalar.distance (sourceCoefficient 50 72 3 2) v3646_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3646_upper : Scalar.QComplex := ((999994585226419509626118912458 : Int)/10^30,(-3290823277115898210327716265 : Int)/10^30)
theorem v3646_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 72 5) 1) 14) v3646_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3646 : Material (50 : Basis) (72 : Basis) where
  plus := ![v3646_pa,v3646_pb,v3646_pg]
  minus := ![(Primitive.Addresses.material3646 1).one,v3646_mb,v3646_mg]
  upper := v3646_upper
  lower := (Primitive.Addresses.material3646 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3646_pa_checked.trans (by decide +kernel)
    · exact v3646_pb_checked.trans (by decide +kernel)
    · exact v3646_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 72 Primitive.Addresses.material3646
    · exact v3646_mb_checked.trans (by decide +kernel)
    · exact v3646_mg_checked.trans (by decide +kernel)
  upper_error := v3646_upper_checked
  lower_error := reuse_lower_error 50 72 Primitive.Addresses.material3646

def v3647_pa : Scalar.QComplex := ((999998760681819750520133396889 : Int)/10^30,(-1574368071509774945462573063 : Int)/10^30)
theorem v3647_pa_checked : Scalar.distance (sourceCoefficient 50 73 1 0) v3647_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3647_pb : Scalar.QComplex := ((-679304412773996534908966 : Int)/10^30,(-431476973645848099576574117 : Int)/10^30)
theorem v3647_pb_checked : Scalar.distance (sourceCoefficient 50 73 1 1) v3647_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3647_pg : Scalar.QComplex := ((-93086313172297311625185 : Int)/10^30,(146552300977955638737 : Int)/10^30)
theorem v3647_pg_checked : Scalar.distance (sourceCoefficient 50 73 1 2) v3647_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3647_mb : Scalar.QComplex := ((-1051649355092778739725451 : Int)/10^30,(-431476226778137850432418610 : Int)/10^30)
theorem v3647_mb_checked : Scalar.distance (sourceCoefficient 50 73 3 1) v3647_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3647_mg : Scalar.QComplex := ((-93086152043973389541821 : Int)/10^30,(226881542225614643832 : Int)/10^30)
theorem v3647_mg_checked : Scalar.distance (sourceCoefficient 50 73 3 2) v3647_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3647_upper : Scalar.QComplex := ((999994554084667950947493671204 : Int)/10^30,(-3300272868431381866805336771 : Int)/10^30)
theorem v3647_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 73 5) 1) 14) v3647_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3647 : Material (50 : Basis) (73 : Basis) where
  plus := ![v3647_pa,v3647_pb,v3647_pg]
  minus := ![(Primitive.Addresses.material3647 1).one,v3647_mb,v3647_mg]
  upper := v3647_upper
  lower := (Primitive.Addresses.material3647 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3647_pa_checked.trans (by decide +kernel)
    · exact v3647_pb_checked.trans (by decide +kernel)
    · exact v3647_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 73 Primitive.Addresses.material3647
    · exact v3647_mb_checked.trans (by decide +kernel)
    · exact v3647_mg_checked.trans (by decide +kernel)
  upper_error := v3647_upper_checked
  lower_error := reuse_lower_error 50 73 Primitive.Addresses.material3647

def v3648_pa : Scalar.QComplex := ((999998743884763149140581883527 : Int)/10^30,(-1585001228982561573881905221 : Int)/10^30)
theorem v3648_pa_checked : Scalar.distance (sourceCoefficient 50 74 1 0) v3648_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3648_pb : Scalar.QComplex := ((-683892380038401884265450 : Int)/10^30,(-431476965749587586609492622 : Int)/10^30)
theorem v3648_pb_checked : Scalar.distance (sourceCoefficient 50 74 1 1) v3648_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3648_pg : Scalar.QComplex := ((-93086311538743528485416 : Int)/10^30,(147542103520246403807 : Int)/10^30)
theorem v3648_pg_checked : Scalar.distance (sourceCoefficient 50 74 1 2) v3648_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3648_mb : Scalar.QComplex := ((-1056237313834757007762559 : Int)/10^30,(-431476214922671162797146788 : Int)/10^30)
theorem v3648_mb_checked : Scalar.distance (sourceCoefficient 50 74 3 1) v3648_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3648_mg : Scalar.QComplex := ((-93086149556265199703505 : Int)/10^30,(227871342989673343879 : Int)/10^30)
theorem v3648_mg_checked : Scalar.distance (sourceCoefficient 50 74 3 2) v3648_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3648_upper : Scalar.QComplex := ((999994518935771201291543943084 : Int)/10^30,(-3310905981077133621017673267 : Int)/10^30)
theorem v3648_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 50 74 5) 1) 14) v3648_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3648 : Material (50 : Basis) (74 : Basis) where
  plus := ![v3648_pa,v3648_pb,v3648_pg]
  minus := ![(Primitive.Addresses.material3648 1).one,v3648_mb,v3648_mg]
  upper := v3648_upper
  lower := (Primitive.Addresses.material3648 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3648_pa_checked.trans (by decide +kernel)
    · exact v3648_pb_checked.trans (by decide +kernel)
    · exact v3648_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 50 74 Primitive.Addresses.material3648
    · exact v3648_mb_checked.trans (by decide +kernel)
    · exact v3648_mg_checked.trans (by decide +kernel)
  upper_error := v3648_upper_checked
  lower_error := reuse_lower_error 50 74 Primitive.Addresses.material3648

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
