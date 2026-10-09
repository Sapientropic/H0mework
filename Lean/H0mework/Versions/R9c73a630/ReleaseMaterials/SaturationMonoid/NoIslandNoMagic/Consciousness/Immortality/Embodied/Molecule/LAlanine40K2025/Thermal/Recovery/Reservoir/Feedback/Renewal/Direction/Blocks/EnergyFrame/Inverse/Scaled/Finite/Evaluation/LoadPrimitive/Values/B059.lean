import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B039
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B040

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v945_pa : Scalar.QComplex := ((999999971168514140662275859578 : Int)/10^30,(-240131153512868611763628918 : Int)/10^30)
theorem v945_pa_checked : Scalar.distance (sourceCoefficient 10 31 1 0) v945_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v945_pb : Scalar.QComplex := ((-103611192756545222506012 : Int)/10^30,(-431477499914346046088618440 : Int)/10^30)
theorem v945_pb_checked : Scalar.distance (sourceCoefficient 10 31 1 1) v945_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v945_pg : Scalar.QComplex := ((-93086426280499079885808 : Int)/10^30,(22352951563595658609 : Int)/10^30)
theorem v945_pg_checked : Scalar.distance (sourceCoefficient 10 31 1 2) v945_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v945_mb : Scalar.QComplex := ((-475956803578235194299880 : Int)/10^30,(-431477249843760458064174251 : Int)/10^30)
theorem v945_mb_checked : Scalar.distance (sourceCoefficient 10 31 3 1) v945_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v945_mg : Scalar.QComplex := ((-93086372330577855993723 : Int)/10^30,(102682336663632563056 : Int)/10^30)
theorem v945_mg_checked : Scalar.distance (sourceCoefficient 10 31 3 2) v945_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v945_upper : Scalar.QComplex := ((999998067341438898332369914737 : Int)/10^30,(-1966040026813854433688883386 : Int)/10^30)
theorem v945_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 31 5) 1) 14) v945_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material945 : Material (10 : Basis) (31 : Basis) where
  plus := ![v945_pa,v945_pb,v945_pg]
  minus := ![(Primitive.Addresses.material945 1).one,v945_mb,v945_mg]
  upper := v945_upper
  lower := (Primitive.Addresses.material945 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v945_pa_checked.trans (by decide +kernel)
    · exact v945_pb_checked.trans (by decide +kernel)
    · exact v945_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 31 Primitive.Addresses.material945
    · exact v945_mb_checked.trans (by decide +kernel)
    · exact v945_mg_checked.trans (by decide +kernel)
  upper_error := v945_upper_checked
  lower_error := reuse_lower_error 10 31 Primitive.Addresses.material945

def v946_pa : Scalar.QComplex := ((999999970010220605783418866587 : Int)/10^30,(-244907243439319887652417353 : Int)/10^30)
theorem v946_pa_checked : Scalar.distance (sourceCoefficient 10 32 1 0) v946_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v946_pb : Scalar.QComplex := ((-105671968098056290691344 : Int)/10^30,(-431477499174741160333711583 : Int)/10^30)
theorem v946_pb_checked : Scalar.distance (sourceCoefficient 10 32 1 1) v946_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v946_pg : Scalar.QComplex := ((-93086426146807650684569 : Int)/10^30,(22797540712925709969 : Int)/10^30)
theorem v946_pg_checked : Scalar.distance (sourceCoefficient 10 32 1 2) v946_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v946_mb : Scalar.QComplex := ((-478017577514179714915868 : Int)/10^30,(-431477247325799541849884759 : Int)/10^30)
theorem v946_mb_checked : Scalar.distance (sourceCoefficient 10 32 3 1) v946_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v946_mg : Scalar.QComplex := ((-93086371813226064252055 : Int)/10^30,(103126925532052073230 : Int)/10^30)
theorem v946_mg_checked : Scalar.distance (sourceCoefficient 10 32 3 2) v946_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v946_upper : Scalar.QComplex := ((999998057940049159034270974538 : Int)/10^30,(-1970816107627771241429833407 : Int)/10^30)
theorem v946_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 32 5) 1) 14) v946_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material946 : Material (10 : Basis) (32 : Basis) where
  plus := ![v946_pa,v946_pb,v946_pg]
  minus := ![(Primitive.Addresses.material946 1).one,v946_mb,v946_mg]
  upper := v946_upper
  lower := (Primitive.Addresses.material946 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v946_pa_checked.trans (by decide +kernel)
    · exact v946_pb_checked.trans (by decide +kernel)
    · exact v946_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 32 Primitive.Addresses.material946
    · exact v946_mb_checked.trans (by decide +kernel)
    · exact v946_mg_checked.trans (by decide +kernel)
  upper_error := v946_upper_checked
  lower_error := reuse_lower_error 10 32 Primitive.Addresses.material946

def v947_pa : Scalar.QComplex := ((999999968357937244943141345753 : Int)/10^30,(-251563360823657271144584651 : Int)/10^30)
theorem v947_pa_checked : Scalar.distance (sourceCoefficient 10 33 1 0) v947_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v947_pb : Scalar.QComplex := ((-108543932981936369980501 : Int)/10^30,(-431477498122114652236442095 : Int)/10^30)
theorem v947_pb_checked : Scalar.distance (sourceCoefficient 10 33 1 1) v947_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v947_pg : Scalar.QComplex := ((-93086425956358896904307 : Int)/10^30,(23417134901610621155 : Int)/10^30)
theorem v947_pg_checked : Scalar.distance (sourceCoefficient 10 33 1 2) v947_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v947_mb : Scalar.QComplex := ((-480889540420326744707230 : Int)/10^30,(-431477243794797079401791274 : Int)/10^30)
theorem v947_mb_checked : Scalar.distance (sourceCoefficient 10 33 3 1) v947_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v947_mg : Scalar.QComplex := ((-93086371088095502035848 : Int)/10^30,(103746519325685054097 : Int)/10^30)
theorem v947_mg_checked : Scalar.distance (sourceCoefficient 10 33 3 2) v947_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v947_upper : Scalar.QComplex := ((999998044799913491961826198790 : Int)/10^30,(-1977472212246912476588949234 : Int)/10^30)
theorem v947_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 33 5) 1) 14) v947_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material947 : Material (10 : Basis) (33 : Basis) where
  plus := ![v947_pa,v947_pb,v947_pg]
  minus := ![(Primitive.Addresses.material947 1).one,v947_mb,v947_mg]
  upper := v947_upper
  lower := (Primitive.Addresses.material947 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v947_pa_checked.trans (by decide +kernel)
    · exact v947_pb_checked.trans (by decide +kernel)
    · exact v947_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 33 Primitive.Addresses.material947
    · exact v947_mb_checked.trans (by decide +kernel)
    · exact v947_mg_checked.trans (by decide +kernel)
  upper_error := v947_upper_checked
  lower_error := reuse_lower_error 10 33 Primitive.Addresses.material947

def v948_pa : Scalar.QComplex := ((999999964160235761219849576473 : Int)/10^30,(-267730325501373863615065203 : Int)/10^30)
theorem v948_pa_checked : Scalar.distance (sourceCoefficient 10 34 1 0) v948_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v948_pb : Scalar.QComplex := ((-115519614446022297465139 : Int)/10^30,(-431477495459264884557081500 : Int)/10^30)
theorem v948_pb_checked : Scalar.distance (sourceCoefficient 10 34 1 1) v948_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v948_pg : Scalar.QComplex := ((-93086425473744407394015 : Int)/10^30,(24922059885045720573 : Int)/10^30)
theorem v948_pg_checked : Scalar.distance (sourceCoefficient 10 34 1 2) v948_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v948_mb : Scalar.QComplex := ((-487865216989128239514738 : Int)/10^30,(-431477235112249372747433344 : Int)/10^30)
theorem v948_mb_checked : Scalar.distance (sourceCoefficient 10 34 3 1) v948_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v948_mg : Scalar.QComplex := ((-93086369306798710825664 : Int)/10^30,(105251443332293235415 : Int)/10^30)
theorem v948_mg_checked : Scalar.distance (sourceCoefficient 10 34 3 2) v948_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v948_upper : Scalar.QComplex := ((999998012699503882061636980910 : Int)/10^30,(-1993639145600982338273923128 : Int)/10^30)
theorem v948_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 34 5) 1) 14) v948_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material948 : Material (10 : Basis) (34 : Basis) where
  plus := ![v948_pa,v948_pb,v948_pg]
  minus := ![(Primitive.Addresses.material948 1).one,v948_mb,v948_mg]
  upper := v948_upper
  lower := (Primitive.Addresses.material948 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v948_pa_checked.trans (by decide +kernel)
    · exact v948_pb_checked.trans (by decide +kernel)
    · exact v948_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 34 Primitive.Addresses.material948
    · exact v948_mb_checked.trans (by decide +kernel)
    · exact v948_mg_checked.trans (by decide +kernel)
  upper_error := v948_upper_checked
  lower_error := reuse_lower_error 10 34 Primitive.Addresses.material948

def v949_pa : Scalar.QComplex := ((999999949090010098219232502579 : Int)/10^30,(-319092427380742558409975984 : Int)/10^30)
theorem v949_pa_checked : Scalar.distance (sourceCoefficient 10 35 1 0) v949_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v949_pb : Scalar.QComplex := ((-137681205377786542370409 : Int)/10^30,(-431477486001746838716677648 : Int)/10^30)
theorem v949_pb_checked : Scalar.distance (sourceCoefficient 10 35 1 1) v949_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v949_pg : Scalar.QComplex := ((-93086423752150998506877 : Int)/10^30,(29703174423454581666 : Int)/10^30)
theorem v949_pg_checked : Scalar.distance (sourceCoefficient 10 35 1 2) v949_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v949_mb : Scalar.QComplex := ((-510026791507707223024025 : Int)/10^30,(-431477206530279995264257898 : Int)/10^30)
theorem v949_mb_checked : Scalar.distance (sourceCoefficient 10 35 3 1) v949_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v949_mg : Scalar.QComplex := ((-93086363459319429724843 : Int)/10^30,(110032554604817071948 : Int)/10^30)
theorem v949_mg_checked : Scalar.distance (sourceCoefficient 10 35 3 2) v949_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v949_upper : Scalar.QComplex := ((999997908982972354085722897367 : Int)/10^30,(-2045001144972691365913706511 : Int)/10^30)
theorem v949_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 35 5) 1) 14) v949_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material949 : Material (10 : Basis) (35 : Basis) where
  plus := ![v949_pa,v949_pb,v949_pg]
  minus := ![(Primitive.Addresses.material949 1).one,v949_mb,v949_mg]
  upper := v949_upper
  lower := (Primitive.Addresses.material949 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v949_pa_checked.trans (by decide +kernel)
    · exact v949_pb_checked.trans (by decide +kernel)
    · exact v949_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 35 Primitive.Addresses.material949
    · exact v949_mb_checked.trans (by decide +kernel)
    · exact v949_mg_checked.trans (by decide +kernel)
  upper_error := v949_upper_checked
  lower_error := reuse_lower_error 10 35 Primitive.Addresses.material949

def v950_pa : Scalar.QComplex := ((999999943807957720391653233725 : Int)/10^30,(-335237350845145353381697736 : Int)/10^30)
theorem v950_pa_checked : Scalar.distance (sourceCoefficient 10 36 1 0) v950_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v950_pb : Scalar.QComplex := ((-144647376382875646955343 : Int)/10^30,(-431477482715404378445948722 : Int)/10^30)
theorem v950_pb_checked : Scalar.distance (sourceCoefficient 10 36 1 1) v950_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v950_pg : Scalar.QComplex := ((-93086423151811558667595 : Int)/10^30,(31206047650595061578 : Int)/10^30)
theorem v950_pg_checked : Scalar.distance (sourceCoefficient 10 36 1 2) v950_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v950_mb : Scalar.QComplex := ((-516992957083006960827900 : Int)/10^30,(-431477197232446925952441607 : Int)/10^30)
theorem v950_mb_checked : Scalar.distance (sourceCoefficient 10 36 3 1) v950_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v950_mg : Scalar.QComplex := ((-93086361562068305294633 : Int)/10^30,(111535426754303266400 : Int)/10^30)
theorem v950_mg_checked : Scalar.distance (sourceCoefficient 10 36 3 2) v950_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v950_upper : Scalar.QComplex := ((999997875836254599710888530584 : Int)/10^30,(-2061146035274783956508706359 : Int)/10^30)
theorem v950_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 36 5) 1) 14) v950_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material950 : Material (10 : Basis) (36 : Basis) where
  plus := ![v950_pa,v950_pb,v950_pg]
  minus := ![(Primitive.Addresses.material950 1).one,v950_mb,v950_mg]
  upper := v950_upper
  lower := (Primitive.Addresses.material950 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v950_pa_checked.trans (by decide +kernel)
    · exact v950_pb_checked.trans (by decide +kernel)
    · exact v950_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 36 Primitive.Addresses.material950
    · exact v950_mb_checked.trans (by decide +kernel)
    · exact v950_mg_checked.trans (by decide +kernel)
  upper_error := v950_upper_checked
  lower_error := reuse_lower_error 10 36 Primitive.Addresses.material950

def v951_pa : Scalar.QComplex := ((999999941473048364087248180538 : Int)/10^30,(-342131407278579783774201039 : Int)/10^30)
theorem v951_pa_checked : Scalar.distance (sourceCoefficient 10 37 1 0) v951_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v951_pb : Scalar.QComplex := ((-147622006514560756667656 : Int)/10^30,(-431477481266412403813391684 : Int)/10^30)
theorem v951_pb_checked : Scalar.distance (sourceCoefficient 10 37 1 1) v951_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v951_pg : Scalar.QComplex := ((-93086422886835497174546 : Int)/10^30,(31847790724756133444 : Int)/10^30)
theorem v951_pg_checked : Scalar.distance (sourceCoefficient 10 37 1 2) v951_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v951_mb : Scalar.QComplex := ((-519967584856686511268965 : Int)/10^30,(-431477193216483659569412279 : Int)/10^30)
theorem v951_mb_checked : Scalar.distance (sourceCoefficient 10 37 3 1) v951_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v951_mg : Scalar.QComplex := ((-93086360743296972498406 : Int)/10^30,(112177169360851655659 : Int)/10^30)
theorem v951_mg_checked : Scalar.distance (sourceCoefficient 10 37 3 2) v951_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v951_upper : Scalar.QComplex := ((999997861602832740785962780759 : Int)/10^30,(-2068040077410489434397688644 : Int)/10^30)
theorem v951_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 37 5) 1) 14) v951_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material951 : Material (10 : Basis) (37 : Basis) where
  plus := ![v951_pa,v951_pb,v951_pg]
  minus := ![(Primitive.Addresses.material951 1).one,v951_mb,v951_mg]
  upper := v951_upper
  lower := (Primitive.Addresses.material951 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v951_pa_checked.trans (by decide +kernel)
    · exact v951_pb_checked.trans (by decide +kernel)
    · exact v951_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 37 Primitive.Addresses.material951
    · exact v951_mb_checked.trans (by decide +kernel)
    · exact v951_mg_checked.trans (by decide +kernel)
  upper_error := v951_upper_checked
  lower_error := reuse_lower_error 10 37 Primitive.Addresses.material951

def v952_pa : Scalar.QComplex := ((999999933229570308589436740440 : Int)/10^30,(-365432421829988759610682557 : Int)/10^30)
theorem v952_pa_checked : Scalar.distance (sourceCoefficient 10 38 1 0) v952_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v952_pb : Scalar.QComplex := ((-157675869608745906592339 : Int)/10^30,(-431477476166623118549374529 : Int)/10^30)
theorem v952_pb_checked : Scalar.distance (sourceCoefficient 10 38 1 1) v952_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v952_pg : Scalar.QComplex := ((-93086421953046391275166 : Int)/10^30,(34016798885106253267 : Int)/10^30)
theorem v952_pg_checked : Scalar.distance (sourceCoefficient 10 38 1 2) v952_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v952_mb : Scalar.QComplex := ((-530021439806470479786347 : Int)/10^30,(-431477179440665232092928573 : Int)/10^30)
theorem v952_mb_checked : Scalar.distance (sourceCoefficient 10 38 3 1) v952_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v952_mg : Scalar.QComplex := ((-93086357937751860410407 : Int)/10^30,(114346175907762966722 : Int)/10^30)
theorem v952_mg_checked : Scalar.distance (sourceCoefficient 10 38 3 2) v952_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v952_upper : Scalar.QComplex := ((999997813143929698776077624026 : Int)/10^30,(-2091341043030279084050712904 : Int)/10^30)
theorem v952_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 38 5) 1) 14) v952_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material952 : Material (10 : Basis) (38 : Basis) where
  plus := ![v952_pa,v952_pb,v952_pg]
  minus := ![(Primitive.Addresses.material952 1).one,v952_mb,v952_mg]
  upper := v952_upper
  lower := (Primitive.Addresses.material952 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v952_pa_checked.trans (by decide +kernel)
    · exact v952_pb_checked.trans (by decide +kernel)
    · exact v952_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 38 Primitive.Addresses.material952
    · exact v952_mb_checked.trans (by decide +kernel)
    · exact v952_mg_checked.trans (by decide +kernel)
  upper_error := v952_upper_checked
  lower_error := reuse_lower_error 10 38 Primitive.Addresses.material952

def v953_pa : Scalar.QComplex := ((999999928198516434894518921606 : Int)/10^30,(-378949814585992270289500959 : Int)/10^30)
theorem v953_pa_checked : Scalar.distance (sourceCoefficient 10 39 1 0) v953_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v953_pb : Scalar.QComplex := ((-163508320156143012211125 : Int)/10^30,(-431477473064970512801724318 : Int)/10^30)
theorem v953_pb_checked : Scalar.distance (sourceCoefficient 10 39 1 1) v953_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v953_pg : Scalar.QComplex := ((-93086421384311609676160 : Int)/10^30,(35275084656861841652 : Int)/10^30)
theorem v953_pg_checked : Scalar.distance (sourceCoefficient 10 39 1 2) v953_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v953_mb : Scalar.QComplex := ((-535853885505593184938516 : Int)/10^30,(-431477171305871642649966813 : Int)/10^30)
theorem v953_mb_checked : Scalar.distance (sourceCoefficient 10 39 3 1) v953_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v953_mg : Scalar.QComplex := ((-93086356283173340639710 : Int)/10^30,(115604460720208754126 : Int)/10^30)
theorem v953_mg_checked : Scalar.distance (sourceCoefficient 10 39 3 2) v953_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v953_upper : Scalar.QComplex := ((999997784783089709674442337219 : Int)/10^30,(-2104858406970571376801505163 : Int)/10^30)
theorem v953_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 39 5) 1) 14) v953_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material953 : Material (10 : Basis) (39 : Basis) where
  plus := ![v953_pa,v953_pb,v953_pg]
  minus := ![(Primitive.Addresses.material953 1).one,v953_mb,v953_mg]
  upper := v953_upper
  lower := (Primitive.Addresses.material953 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v953_pa_checked.trans (by decide +kernel)
    · exact v953_pb_checked.trans (by decide +kernel)
    · exact v953_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 39 Primitive.Addresses.material953
    · exact v953_mb_checked.trans (by decide +kernel)
    · exact v953_mg_checked.trans (by decide +kernel)
  upper_error := v953_upper_checked
  lower_error := reuse_lower_error 10 39 Primitive.Addresses.material953

def v954_pa : Scalar.QComplex := ((999999919324452007541693725209 : Int)/10^30,(-401685311501892696064062091 : Int)/10^30)
theorem v954_pa_checked : Scalar.distance (sourceCoefficient 10 40 1 0) v954_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v954_pb : Scalar.QComplex := ((-173318174965940920253519 : Int)/10^30,(-431477467611074252882625836 : Int)/10^30)
theorem v954_pb_checked : Scalar.distance (sourceCoefficient 10 40 1 1) v954_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v954_pg : Scalar.QComplex := ((-93086420382975684867304 : Int)/10^30,(37391450784707503864 : Int)/10^30)
theorem v954_pg_checked : Scalar.distance (sourceCoefficient 10 40 1 2) v954_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v954_mb : Scalar.QComplex := ((-545663731956266976839254 : Int)/10^30,(-431477157386514532069630650 : Int)/10^30)
theorem v954_mb_checked : Scalar.distance (sourceCoefficient 10 40 3 1) v954_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v954_mg : Scalar.QComplex := ((-93086353455509137935219 : Int)/10^30,(117720825195926779616 : Int)/10^30)
theorem v954_mg_checked : Scalar.distance (sourceCoefficient 10 40 3 2) v954_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v954_upper : Scalar.QComplex := ((999997736669633370522494343294 : Int)/10^30,(-2127593854708789692641678159 : Int)/10^30)
theorem v954_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 40 5) 1) 14) v954_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material954 : Material (10 : Basis) (40 : Basis) where
  plus := ![v954_pa,v954_pb,v954_pg]
  minus := ![(Primitive.Addresses.material954 1).one,v954_mb,v954_mg]
  upper := v954_upper
  lower := (Primitive.Addresses.material954 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v954_pa_checked.trans (by decide +kernel)
    · exact v954_pb_checked.trans (by decide +kernel)
    · exact v954_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 40 Primitive.Addresses.material954
    · exact v954_mb_checked.trans (by decide +kernel)
    · exact v954_mg_checked.trans (by decide +kernel)
  upper_error := v954_upper_checked
  lower_error := reuse_lower_error 10 40 Primitive.Addresses.material954

def v955_pa : Scalar.QComplex := ((999999913401551184545632643432 : Int)/10^30,(-416169304648501674512870070 : Int)/10^30)
theorem v955_pa_checked : Scalar.distance (sourceCoefficient 10 41 1 0) v955_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v955_pb : Scalar.QComplex := ((-179567691706970694153839 : Int)/10^30,(-431477463981517668712698741 : Int)/10^30)
theorem v955_pb_checked : Scalar.distance (sourceCoefficient 10 41 1 1) v955_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v955_pg : Scalar.QComplex := ((-93086419715786801256049 : Int)/10^30,(38739713920136702990 : Int)/10^30)
theorem v955_pg_checked : Scalar.distance (sourceCoefficient 10 41 1 2) v955_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v955_mb : Scalar.QComplex := ((-551913243238172188051000 : Int)/10^30,(-431477148363907819626244542 : Int)/10^30)
theorem v955_mb_checked : Scalar.distance (sourceCoefficient 10 41 3 1) v955_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v955_mg : Scalar.QComplex := ((-93086351624830140390935 : Int)/10^30,(119069087253582037267 : Int)/10^30)
theorem v955_mg_checked : Scalar.distance (sourceCoefficient 10 41 3 2) v955_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v955_upper : Scalar.QComplex := ((999997705748683175538390193238 : Int)/10^30,(-2142077816060802789443038392 : Int)/10^30)
theorem v955_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 41 5) 1) 14) v955_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material955 : Material (10 : Basis) (41 : Basis) where
  plus := ![v955_pa,v955_pb,v955_pg]
  minus := ![(Primitive.Addresses.material955 1).one,v955_mb,v955_mg]
  upper := v955_upper
  lower := (Primitive.Addresses.material955 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v955_pa_checked.trans (by decide +kernel)
    · exact v955_pb_checked.trans (by decide +kernel)
    · exact v955_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 41 Primitive.Addresses.material955
    · exact v955_mb_checked.trans (by decide +kernel)
    · exact v955_mg_checked.trans (by decide +kernel)
  upper_error := v955_upper_checked
  lower_error := reuse_lower_error 10 41 Primitive.Addresses.material955

def v956_pa : Scalar.QComplex := ((999999908470920879267977162874 : Int)/10^30,(-427852953552843574366300256 : Int)/10^30)
theorem v956_pa_checked : Scalar.distance (sourceCoefficient 10 42 1 0) v956_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v956_pb : Scalar.QComplex := ((-184608922962765637206704 : Int)/10^30,(-431477460965757034697387722 : Int)/10^30)
theorem v956_pb_checked : Scalar.distance (sourceCoefficient 10 42 1 1) v956_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v956_pg : Scalar.QComplex := ((-93086419160991169410324 : Int)/10^30,(39827303019044452129 : Int)/10^30)
theorem v956_pg_checked : Scalar.distance (sourceCoefficient 10 42 1 2) v956_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v956_mb : Scalar.QComplex := ((-556954470014420736582931 : Int)/10^30,(-431477140997792783392728558 : Int)/10^30)
theorem v956_mb_checked : Scalar.distance (sourceCoefficient 10 42 3 1) v956_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v956_mg : Scalar.QComplex := ((-93086350131494305958265 : Int)/10^30,(120156675468767016391 : Int)/10^30)
theorem v956_mg_checked : Scalar.distance (sourceCoefficient 10 42 3 2) v956_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v956_upper : Scalar.QComplex := ((999997680653142137310127521491 : Int)/10^30,(-2153761439053901500467335477 : Int)/10^30)
theorem v956_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 42 5) 1) 14) v956_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material956 : Material (10 : Basis) (42 : Basis) where
  plus := ![v956_pa,v956_pb,v956_pg]
  minus := ![(Primitive.Addresses.material956 1).one,v956_mb,v956_mg]
  upper := v956_upper
  lower := (Primitive.Addresses.material956 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v956_pa_checked.trans (by decide +kernel)
    · exact v956_pb_checked.trans (by decide +kernel)
    · exact v956_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 42 Primitive.Addresses.material956
    · exact v956_mb_checked.trans (by decide +kernel)
    · exact v956_mg_checked.trans (by decide +kernel)
  upper_error := v956_upper_checked
  lower_error := reuse_lower_error 10 42 Primitive.Addresses.material956

def v957_pa : Scalar.QComplex := ((999999901728922399350165924351 : Int)/10^30,(-443330740580996678710796430 : Int)/10^30)
theorem v957_pa_checked : Scalar.distance (sourceCoefficient 10 43 1 0) v957_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v957_pb : Scalar.QComplex := ((-191287239287200042911759 : Int)/10^30,(-431477456849732408668468788 : Int)/10^30)
theorem v957_pb_checked : Scalar.distance (sourceCoefficient 10 43 1 1) v957_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v957_pg : Scalar.QComplex := ((-93086418403203838743946 : Int)/10^30,(41268074864183063534 : Int)/10^30)
theorem v957_pg_checked : Scalar.distance (sourceCoefficient 10 43 1 2) v957_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v957_mb : Scalar.QComplex := ((-563632780300268887171758 : Int)/10^30,(-431477131118683482162763986 : Int)/10^30)
theorem v957_mb_checked : Scalar.distance (sourceCoefficient 10 43 3 1) v957_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v957_mg : Scalar.QComplex := ((-93086348130386045051198 : Int)/10^30,(121597446123504086434 : Int)/10^30)
theorem v957_mg_checked : Scalar.distance (sourceCoefficient 10 43 3 2) v957_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v957_upper : Scalar.QComplex := ((999997647197897422085525432471 : Int)/10^30,(-2169239191393631227946251434 : Int)/10^30)
theorem v957_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 43 5) 1) 14) v957_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material957 : Material (10 : Basis) (43 : Basis) where
  plus := ![v957_pa,v957_pb,v957_pg]
  minus := ![(Primitive.Addresses.material957 1).one,v957_mb,v957_mg]
  upper := v957_upper
  lower := (Primitive.Addresses.material957 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v957_pa_checked.trans (by decide +kernel)
    · exact v957_pb_checked.trans (by decide +kernel)
    · exact v957_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 43 Primitive.Addresses.material957
    · exact v957_mb_checked.trans (by decide +kernel)
    · exact v957_mg_checked.trans (by decide +kernel)
  upper_error := v957_upper_checked
  lower_error := reuse_lower_error 10 43 Primitive.Addresses.material957

def v958_pa : Scalar.QComplex := ((999999899115730295340246654321 : Int)/10^30,(-449186519423372313706485977 : Int)/10^30)
theorem v958_pa_checked : Scalar.distance (sourceCoefficient 10 44 1 0) v958_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v958_pb : Scalar.QComplex := ((-193813875889121183229619 : Int)/10^30,(-431477455256564026539512464 : Int)/10^30)
theorem v958_pb_checked : Scalar.distance (sourceCoefficient 10 44 1 1) v958_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v958_pg : Scalar.QComplex := ((-93086418109723382888046 : Int)/10^30,(41813168374586374130 : Int)/10^30)
theorem v958_pg_checked : Scalar.distance (sourceCoefficient 10 44 1 2) v958_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v958_mb : Scalar.QComplex := ((-566159414586575187460210 : Int)/10^30,(-431477127345142101273527067 : Int)/10^30)
theorem v958_mb_checked : Scalar.distance (sourceCoefficient 10 44 3 1) v958_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v958_mg : Scalar.QComplex := ((-93086347366514549093793 : Int)/10^30,(122142539177683755568 : Int)/10^30)
theorem v958_mg_checked : Scalar.distance (sourceCoefficient 10 44 3 2) v958_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v958_upper : Scalar.QComplex := ((999997634478166160284754805977 : Int)/10^30,(-2175094957004379640741046722 : Int)/10^30)
theorem v958_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 44 5) 1) 14) v958_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material958 : Material (10 : Basis) (44 : Basis) where
  plus := ![v958_pa,v958_pb,v958_pg]
  minus := ![(Primitive.Addresses.material958 1).one,v958_mb,v958_mg]
  upper := v958_upper
  lower := (Primitive.Addresses.material958 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v958_pa_checked.trans (by decide +kernel)
    · exact v958_pb_checked.trans (by decide +kernel)
    · exact v958_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 44 Primitive.Addresses.material958
    · exact v958_mb_checked.trans (by decide +kernel)
    · exact v958_mg_checked.trans (by decide +kernel)
  upper_error := v958_upper_checked
  lower_error := reuse_lower_error 10 44 Primitive.Addresses.material958

def v959_pa : Scalar.QComplex := ((999999897802860952284892301556 : Int)/10^30,(-452099842569287990964155158 : Int)/10^30)
theorem v959_pa_checked : Scalar.distance (sourceCoefficient 10 45 1 0) v959_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v959_pb : Scalar.QComplex := ((-195070909167712170278143 : Int)/10^30,(-431477454456594144767111549 : Int)/10^30)
theorem v959_pb_checked : Scalar.distance (sourceCoefficient 10 45 1 1) v959_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v959_pg : Scalar.QComplex := ((-93086417962325963446777 : Int)/10^30,(42084359207007619507 : Int)/10^30)
theorem v959_pg_checked : Scalar.distance (sourceCoefficient 10 45 1 2) v959_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v959_mb : Scalar.QComplex := ((-567416446706777256966849 : Int)/10^30,(-431477125460409412619683873 : Int)/10^30)
theorem v959_mb_checked : Scalar.distance (sourceCoefficient 10 45 3 1) v959_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v959_mg : Scalar.QComplex := ((-93086346985091710137473 : Int)/10^30,(122413729781930925557 : Int)/10^30)
theorem v959_mg_checked : Scalar.distance (sourceCoefficient 10 45 3 2) v959_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v959_upper : Scalar.QComplex := ((999997628137167317354848787740 : Int)/10^30,(-2178008273545349331596768918 : Int)/10^30)
theorem v959_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 45 5) 1) 14) v959_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material959 : Material (10 : Basis) (45 : Basis) where
  plus := ![v959_pa,v959_pb,v959_pg]
  minus := ![(Primitive.Addresses.material959 1).one,v959_mb,v959_mg]
  upper := v959_upper
  lower := (Primitive.Addresses.material959 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v959_pa_checked.trans (by decide +kernel)
    · exact v959_pb_checked.trans (by decide +kernel)
    · exact v959_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 45 Primitive.Addresses.material959
    · exact v959_mb_checked.trans (by decide +kernel)
    · exact v959_mg_checked.trans (by decide +kernel)
  upper_error := v959_upper_checked
  lower_error := reuse_lower_error 10 45 Primitive.Addresses.material959

def v960_pa : Scalar.QComplex := ((999999890270694946853648344761 : Int)/10^30,(-468464084072378291287310879 : Int)/10^30)
theorem v960_pa_checked : Scalar.distance (sourceCoefficient 10 46 1 0) v960_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v960_pb : Scalar.QComplex := ((-202131710532127285733244 : Int)/10^30,(-431477449872390984168605430 : Int)/10^30)
theorem v960_pb_checked : Scalar.distance (sourceCoefficient 10 46 1 1) v960_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v960_pg : Scalar.QComplex := ((-93086417117259564935959 : Int)/10^30,(43607647919453259695 : Int)/10^30)
theorem v960_pg_checked : Scalar.distance (sourceCoefficient 10 46 1 2) v960_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v960_mb : Scalar.QComplex := ((-574477241486172467135921 : Int)/10^30,(-431477114783054388127768325 : Int)/10^30)
theorem v960_mb_checked : Scalar.distance (sourceCoefficient 10 46 3 1) v960_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v960_mg : Scalar.QComplex := ((-93086344825496073819729 : Int)/10^30,(123937017197932318831 : Int)/10^30)
theorem v960_mg_checked : Scalar.distance (sourceCoefficient 10 46 3 2) v960_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v960_upper : Scalar.QComplex := ((999997592361816248258694660447 : Int)/10^30,(-2194372477675988979294538177 : Int)/10^30)
theorem v960_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 46 5) 1) 14) v960_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material960 : Material (10 : Basis) (46 : Basis) where
  plus := ![v960_pa,v960_pb,v960_pg]
  minus := ![(Primitive.Addresses.material960 1).one,v960_mb,v960_mg]
  upper := v960_upper
  lower := (Primitive.Addresses.material960 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v960_pa_checked.trans (by decide +kernel)
    · exact v960_pb_checked.trans (by decide +kernel)
    · exact v960_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 46 Primitive.Addresses.material960
    · exact v960_mb_checked.trans (by decide +kernel)
    · exact v960_mg_checked.trans (by decide +kernel)
  upper_error := v960_upper_checked
  lower_error := reuse_lower_error 10 46 Primitive.Addresses.material960

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
