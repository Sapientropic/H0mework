import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B121
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B122

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2913_pa : Scalar.QComplex := ((999998640809734417351491584585 : Int)/10^30,(-1648750643295437493003894953 : Int)/10^30)
theorem v2913_pa_checked : Scalar.distance (sourceCoefficient 36 88 1 0) v2913_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2913_pb : Scalar.QComplex := ((-711398750230706313320230 : Int)/10^30,(-431476879901344550617462765 : Int)/10^30)
theorem v2913_pb_checked : Scalar.distance (sourceCoefficient 36 88 1 1) v2913_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2913_pg : Scalar.QComplex := ((-93086297480903078840783 : Int)/10^30,(153476301457124351972 : Int)/10^30)
theorem v2913_pg_checked : Scalar.distance (sourceCoefficient 36 88 1 2) v2913_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2913_mb : Scalar.QComplex := ((-1083743599702015432277880 : Int)/10^30,(-431476105337701456996260041 : Int)/10^30)
theorem v2913_mb_checked : Scalar.distance (sourceCoefficient 36 88 3 1) v2913_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2913_mg : Scalar.QComplex := ((-93086130377484431263361 : Int)/10^30,(233805526585695027487 : Int)/10^30)
theorem v2913_mg_checked : Scalar.distance (sourceCoefficient 36 88 3 2) v2913_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2913_upper : Scalar.QComplex := ((999994305835190185315660346847 : Int)/10^30,(-3374655122544596755850277255 : Int)/10^30)
theorem v2913_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 88 5) 1) 14) v2913_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2913 : Material (36 : Basis) (88 : Basis) where
  plus := ![v2913_pa,v2913_pb,v2913_pg]
  minus := ![(Primitive.Addresses.material2913 1).one,v2913_mb,v2913_mg]
  upper := v2913_upper
  lower := (Primitive.Addresses.material2913 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2913_pa_checked.trans (by decide +kernel)
    · exact v2913_pb_checked.trans (by decide +kernel)
    · exact v2913_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 88 Primitive.Addresses.material2913
    · exact v2913_mb_checked.trans (by decide +kernel)
    · exact v2913_mg_checked.trans (by decide +kernel)
  upper_error := v2913_upper_checked
  lower_error := reuse_lower_error 36 88 Primitive.Addresses.material2913

def v2914_pa : Scalar.QComplex := ((999998614152750873418501442000 : Int)/10^30,(-1664840105740057274105332233 : Int)/10^30)
theorem v2914_pa_checked : Scalar.distance (sourceCoefficient 36 89 1 0) v2914_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2914_pb : Scalar.QComplex := ((-718340987332277912319910 : Int)/10^30,(-431476866363739531280319398 : Int)/10^30)
theorem v2914_pb_checked : Scalar.distance (sourceCoefficient 36 89 1 1) v2914_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2914_pg : Scalar.QComplex := ((-93086294779908228782052 : Int)/10^30,(154974011614640239327 : Int)/10^30)
theorem v2914_pg_checked : Scalar.distance (sourceCoefficient 36 89 1 2) v2914_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2914_mb : Scalar.QComplex := ((-1090685822536331461861741 : Int)/10^30,(-431476085809263526424193909 : Int)/10^30)
theorem v2914_mb_checked : Scalar.distance (sourceCoefficient 36 89 3 1) v2914_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2914_mg : Scalar.QComplex := ((-93086126384034175333714 : Int)/10^30,(235303233854708067156 : Int)/10^30)
theorem v2914_mg_checked : Scalar.distance (sourceCoefficient 36 89 3 2) v2914_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2914_upper : Scalar.QComplex := ((999994251409293789045581469398 : Int)/10^30,(-3390744515018316932542647303 : Int)/10^30)
theorem v2914_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 89 5) 1) 14) v2914_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2914 : Material (36 : Basis) (89 : Basis) where
  plus := ![v2914_pa,v2914_pb,v2914_pg]
  minus := ![(Primitive.Addresses.material2914 1).one,v2914_mb,v2914_mg]
  upper := v2914_upper
  lower := (Primitive.Addresses.material2914 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2914_pa_checked.trans (by decide +kernel)
    · exact v2914_pb_checked.trans (by decide +kernel)
    · exact v2914_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 89 Primitive.Addresses.material2914
    · exact v2914_mb_checked.trans (by decide +kernel)
    · exact v2914_mg_checked.trans (by decide +kernel)
  upper_error := v2914_upper_checked
  lower_error := reuse_lower_error 36 89 Primitive.Addresses.material2914

def v2915_pa : Scalar.QComplex := ((999998570185746078116495865982 : Int)/10^30,(-1691043010533725688559161836 : Int)/10^30)
theorem v2915_pa_checked : Scalar.distance (sourceCoefficient 36 90 1 0) v2915_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2915_pb : Scalar.QComplex := ((-729646944509495280463628 : Int)/10^30,(-431476843997955684508318245 : Int)/10^30)
theorem v2915_pb_checked : Scalar.distance (sourceCoefficient 36 90 1 1) v2915_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2915_pg : Scalar.QComplex := ((-93086290320959112803529 : Int)/10^30,(157413145695330578465 : Int)/10^30)
theorem v2915_pg_checked : Scalar.distance (sourceCoefficient 36 90 1 2) v2915_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2915_mb : Scalar.QComplex := ((-1101991756203160122905390 : Int)/10^30,(-431476053686956164925914078 : Int)/10^30)
theorem v2915_mb_checked : Scalar.distance (sourceCoefficient 36 90 3 1) v2915_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2915_mg : Scalar.QComplex := ((-93086119820223862510971 : Int)/10^30,(237742363179325050642 : Int)/10^30)
theorem v2915_mg_checked : Scalar.distance (sourceCoefficient 36 90 3 2) v2915_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2915_upper : Scalar.QComplex := ((999994162218517912514733447785 : Int)/10^30,(-3416947304902775045068907588 : Int)/10^30)
theorem v2915_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 90 5) 1) 14) v2915_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2915 : Material (36 : Basis) (90 : Basis) where
  plus := ![v2915_pa,v2915_pb,v2915_pg]
  minus := ![(Primitive.Addresses.material2915 1).one,v2915_mb,v2915_mg]
  upper := v2915_upper
  lower := (Primitive.Addresses.material2915 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2915_pa_checked.trans (by decide +kernel)
    · exact v2915_pb_checked.trans (by decide +kernel)
    · exact v2915_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 90 Primitive.Addresses.material2915
    · exact v2915_mb_checked.trans (by decide +kernel)
    · exact v2915_mg_checked.trans (by decide +kernel)
  upper_error := v2915_upper_checked
  lower_error := reuse_lower_error 36 90 Primitive.Addresses.material2915

def v2916_pa : Scalar.QComplex := ((999998545115195704405246362241 : Int)/10^30,(-1705804060231243480857642468 : Int)/10^30)
theorem v2916_pa_checked : Scalar.distance (sourceCoefficient 36 91 1 0) v2916_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2916_pb : Scalar.QComplex := ((-736016001417062782837271 : Int)/10^30,(-431476831224560690977544146 : Int)/10^30)
theorem v2916_pb_checked : Scalar.distance (sourceCoefficient 36 91 1 1) v2916_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2916_pg : Scalar.QComplex := ((-93086287776236828103850 : Int)/10^30,(158787198657641193775 : Int)/10^30)
theorem v2916_pg_checked : Scalar.distance (sourceCoefficient 36 91 1 2) v2916_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2916_mb : Scalar.QComplex := ((-1108360799716372071248913 : Int)/10^30,(-431476035417356667957796654 : Int)/10^30)
theorem v2916_mb_checked : Scalar.distance (sourceCoefficient 36 91 3 1) v2916_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2916_mg : Scalar.QComplex := ((-93086116089756703901779 : Int)/10^30,(239116413434032229102 : Int)/10^30)
theorem v2916_mg_checked : Scalar.distance (sourceCoefficient 36 91 3 2) v2916_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2916_upper : Scalar.QComplex := ((999994111671772212495552537707 : Int)/10^30,(-3431708289345947705153566285 : Int)/10^30)
theorem v2916_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 91 5) 1) 14) v2916_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2916 : Material (36 : Basis) (91 : Basis) where
  plus := ![v2916_pa,v2916_pb,v2916_pg]
  minus := ![(Primitive.Addresses.material2916 1).one,v2916_mb,v2916_mg]
  upper := v2916_upper
  lower := (Primitive.Addresses.material2916 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2916_pa_checked.trans (by decide +kernel)
    · exact v2916_pb_checked.trans (by decide +kernel)
    · exact v2916_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 91 Primitive.Addresses.material2916
    · exact v2916_mb_checked.trans (by decide +kernel)
    · exact v2916_mg_checked.trans (by decide +kernel)
  upper_error := v2916_upper_checked
  lower_error := reuse_lower_error 36 91 Primitive.Addresses.material2916

def v2917_pa : Scalar.QComplex := ((999998490093747102699696768325 : Int)/10^30,(-1737760117501178028487918919 : Int)/10^30)
theorem v2917_pa_checked : Scalar.distance (sourceCoefficient 36 92 1 0) v2917_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2917_pb : Scalar.QComplex := ((-749804312261508537578683 : Int)/10^30,(-431476803142123390687764735 : Int)/10^30)
theorem v2917_pb_checked : Scalar.distance (sourceCoefficient 36 92 1 1) v2917_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2917_pg : Scalar.QComplex := ((-93086282186126460993680 : Int)/10^30,(161761872914774328415 : Int)/10^30)
theorem v2917_pg_checked : Scalar.distance (sourceCoefficient 36 92 1 2) v2917_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2917_mb : Scalar.QComplex := ((-1122149081192920937542056 : Int)/10^30,(-431475995436238567753907219 : Int)/10^30)
theorem v2917_mb_checked : Scalar.distance (sourceCoefficient 36 92 3 1) v2917_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2917_mg : Scalar.QComplex := ((-93086107932638508694463 : Int)/10^30,(242091081759544710890 : Int)/10^30)
theorem v2917_mg_checked : Scalar.distance (sourceCoefficient 36 92 3 2) v2917_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2917_upper : Scalar.QComplex := ((999994001497149741736934686000 : Int)/10^30,(-3463664204059059991676743061 : Int)/10^30)
theorem v2917_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 92 5) 1) 14) v2917_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2917 : Material (36 : Basis) (92 : Basis) where
  plus := ![v2917_pa,v2917_pb,v2917_pg]
  minus := ![(Primitive.Addresses.material2917 1).one,v2917_mb,v2917_mg]
  upper := v2917_upper
  lower := (Primitive.Addresses.material2917 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2917_pa_checked.trans (by decide +kernel)
    · exact v2917_pb_checked.trans (by decide +kernel)
    · exact v2917_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 92 Primitive.Addresses.material2917
    · exact v2917_mb_checked.trans (by decide +kernel)
    · exact v2917_mg_checked.trans (by decide +kernel)
  upper_error := v2917_upper_checked
  lower_error := reuse_lower_error 36 92 Primitive.Addresses.material2917

def v2918_pa : Scalar.QComplex := ((999998423468956748977896115002 : Int)/10^30,(-1775685670678207019926534728 : Int)/10^30)
theorem v2918_pa_checked : Scalar.distance (sourceCoefficient 36 93 1 0) v2918_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2918_pb : Scalar.QComplex := ((-766168323923300874267997 : Int)/10^30,(-431476769051429738616707830 : Int)/10^30)
theorem v2918_pb_checked : Scalar.distance (sourceCoefficient 36 93 1 1) v2918_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2918_pg : Scalar.QComplex := ((-93086275407852341879597 : Int)/10^30,(165292225966854019200 : Int)/10^30)
theorem v2918_pg_checked : Scalar.distance (sourceCoefficient 36 93 1 2) v2918_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2918_mb : Scalar.QComplex := ((-1138513057342910626375991 : Int)/10^30,(-431475947224152552805566392 : Int)/10^30)
theorem v2918_mb_checked : Scalar.distance (sourceCoefficient 36 93 3 1) v2918_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2918_mg : Scalar.QComplex := ((-93086098107831230695908 : Int)/10^30,(245621427647767332620 : Int)/10^30)
theorem v2918_mg_checked : Scalar.distance (sourceCoefficient 36 93 3 2) v2918_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2918_upper : Scalar.QComplex := ((999993869416394413569918482533 : Int)/10^30,(-3501589585762088577599656666 : Int)/10^30)
theorem v2918_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 93 5) 1) 14) v2918_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2918 : Material (36 : Basis) (93 : Basis) where
  plus := ![v2918_pa,v2918_pb,v2918_pg]
  minus := ![(Primitive.Addresses.material2918 1).one,v2918_mb,v2918_mg]
  upper := v2918_upper
  lower := (Primitive.Addresses.material2918 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2918_pa_checked.trans (by decide +kernel)
    · exact v2918_pb_checked.trans (by decide +kernel)
    · exact v2918_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 93 Primitive.Addresses.material2918
    · exact v2918_mb_checked.trans (by decide +kernel)
    · exact v2918_mg_checked.trans (by decide +kernel)
  upper_error := v2918_upper_checked
  lower_error := reuse_lower_error 36 93 Primitive.Addresses.material2918

def v2919_pa : Scalar.QComplex := ((999998342917346366662418231408 : Int)/10^30,(-1820484155751912659593557862 : Int)/10^30)
theorem v2919_pa_checked : Scalar.distance (sourceCoefficient 36 94 1 0) v2919_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2919_pb : Scalar.QComplex := ((-785497848018881372637728 : Int)/10^30,(-431476727716748592268552353 : Int)/10^30)
theorem v2919_pb_checked : Scalar.distance (sourceCoefficient 36 94 1 1) v2919_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2919_pg : Scalar.QComplex := ((-93086267199974761725533 : Int)/10^30,(169462355368772538304 : Int)/10^30)
theorem v2919_pg_checked : Scalar.distance (sourceCoefficient 36 94 1 2) v2919_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2919_mb : Scalar.QComplex := ((-1157842538571257716701810 : Int)/10^30,(-431475889208978072210527811 : Int)/10^30)
theorem v2919_mb_checked : Scalar.distance (sourceCoefficient 36 94 3 1) v2919_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2919_mg : Scalar.QComplex := ((-93086086301322848510321 : Int)/10^30,(249791548413927408472 : Int)/10^30)
theorem v2919_mg_checked : Scalar.distance (sourceCoefficient 36 94 3 2) v2919_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2919_upper : Scalar.QComplex := ((999993711546782853018896714521 : Int)/10^30,(-3546387865088941164835952728 : Int)/10^30)
theorem v2919_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 94 5) 1) 14) v2919_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2919 : Material (36 : Basis) (94 : Basis) where
  plus := ![v2919_pa,v2919_pb,v2919_pg]
  minus := ![(Primitive.Addresses.material2919 1).one,v2919_mb,v2919_mg]
  upper := v2919_upper
  lower := (Primitive.Addresses.material2919 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2919_pa_checked.trans (by decide +kernel)
    · exact v2919_pb_checked.trans (by decide +kernel)
    · exact v2919_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 94 Primitive.Addresses.material2919
    · exact v2919_mb_checked.trans (by decide +kernel)
    · exact v2919_mg_checked.trans (by decide +kernel)
  upper_error := v2919_upper_checked
  lower_error := reuse_lower_error 36 94 Primitive.Addresses.material2919

def v2920_pa : Scalar.QComplex := ((999998261336721869589973131508 : Int)/10^30,(-1864758304261124703506150539 : Int)/10^30)
theorem v2920_pa_checked : Scalar.distance (sourceCoefficient 36 95 1 0) v2920_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2920_pb : Scalar.QComplex := ((-804601131743269537171646 : Int)/10^30,(-431476685731471080420123074 : Int)/10^30)
theorem v2920_pb_checked : Scalar.distance (sourceCoefficient 36 95 1 1) v2920_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2920_pg : Scalar.QComplex := ((-93086258874024123603275 : Int)/10^30,(173583676051500529764 : Int)/10^30)
theorem v2920_pg_checked : Scalar.distance (sourceCoefficient 36 95 1 2) v2920_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2920_mb : Scalar.QComplex := ((-1176945778951216741428312 : Int)/10^30,(-431475830738442719212893200 : Int)/10^30)
theorem v2920_mb_checked : Scalar.distance (sourceCoefficient 36 95 3 1) v2920_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2920_mg : Scalar.QComplex := ((-93086074418861178718852 : Int)/10^30,(253912860377178942288 : Int)/10^30)
theorem v2920_mg_checked : Scalar.distance (sourceCoefficient 36 95 3 2) v2920_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2920_upper : Scalar.QComplex := ((999993553553116053180947046721 : Int)/10^30,(-3590661806856252865592242555 : Int)/10^30)
theorem v2920_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 95 5) 1) 14) v2920_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2920 : Material (36 : Basis) (95 : Basis) where
  plus := ![v2920_pa,v2920_pb,v2920_pg]
  minus := ![(Primitive.Addresses.material2920 1).one,v2920_mb,v2920_mg]
  upper := v2920_upper
  lower := (Primitive.Addresses.material2920 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2920_pa_checked.trans (by decide +kernel)
    · exact v2920_pb_checked.trans (by decide +kernel)
    · exact v2920_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 95 Primitive.Addresses.material2920
    · exact v2920_mb_checked.trans (by decide +kernel)
    · exact v2920_mg_checked.trans (by decide +kernel)
  upper_error := v2920_upper_checked
  lower_error := reuse_lower_error 36 95 Primitive.Addresses.material2920

def v2921_pa : Scalar.QComplex := ((999998221458240553832975490209 : Int)/10^30,(-1886022363515752152268125243 : Int)/10^30)
theorem v2921_pa_checked : Scalar.distance (sourceCoefficient 36 96 1 0) v2921_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2921_pb : Scalar.QComplex := ((-813776087172724833659555 : Int)/10^30,(-431476665165839255508012167 : Int)/10^30)
theorem v2921_pb_checked : Scalar.distance (sourceCoefficient 36 96 1 1) v2921_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2921_pg : Scalar.QComplex := ((-93086254799549322049359 : Int)/10^30,(175563070534127901505 : Int)/10^30)
theorem v2921_pg_checked : Scalar.distance (sourceCoefficient 36 96 1 2) v2921_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2921_mb : Scalar.QComplex := ((-1186120713217202792126783 : Int)/10^30,(-431475802255245240858408150 : Int)/10^30)
theorem v2921_mb_checked : Scalar.distance (sourceCoefficient 36 96 3 1) v2921_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2921_mg : Scalar.QComplex := ((-93086068636259604388842 : Int)/10^30,(255892250606699039143 : Int)/10^30)
theorem v2921_mg_checked : Scalar.distance (sourceCoefficient 36 96 3 2) v2921_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2921_upper : Scalar.QComplex := ((999993476974856918637024206118 : Int)/10^30,(-3611925765613920903019298710 : Int)/10^30)
theorem v2921_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 96 5) 1) 14) v2921_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2921 : Material (36 : Basis) (96 : Basis) where
  plus := ![v2921_pa,v2921_pb,v2921_pg]
  minus := ![(Primitive.Addresses.material2921 1).one,v2921_mb,v2921_mg]
  upper := v2921_upper
  lower := (Primitive.Addresses.material2921 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2921_pa_checked.trans (by decide +kernel)
    · exact v2921_pb_checked.trans (by decide +kernel)
    · exact v2921_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 96 Primitive.Addresses.material2921
    · exact v2921_mb_checked.trans (by decide +kernel)
    · exact v2921_mg_checked.trans (by decide +kernel)
  upper_error := v2921_upper_checked
  lower_error := reuse_lower_error 36 96 Primitive.Addresses.material2921

def v2922_pa : Scalar.QComplex := ((999998080796300665594368712007 : Int)/10^30,(-1959184451583355059091379301 : Int)/10^30)
theorem v2922_pa_checked : Scalar.distance (sourceCoefficient 36 97 1 0) v2922_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2922_pb : Scalar.QComplex := ((-845343853477636871706450 : Int)/10^30,(-431476592419567959686988789 : Int)/10^30)
theorem v2922_pb_checked : Scalar.distance (sourceCoefficient 36 97 1 1) v2922_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2922_pg : Scalar.QComplex := ((-93086240405594808512872 : Int)/10^30,(182373464870820052028 : Int)/10^30)
theorem v2922_pg_checked : Scalar.distance (sourceCoefficient 36 97 1 2) v2922_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2922_mb : Scalar.QComplex := ((-1217688404991236958804101 : Int)/10^30,(-431475702267440470075951060 : Int)/10^30)
theorem v2922_mb_checked : Scalar.distance (sourceCoefficient 36 97 3 1) v2922_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2922_mg : Scalar.QComplex := ((-93086048365246866588748 : Int)/10^30,(262702629986235662182 : Int)/10^30)
theorem v2922_mg_checked : Scalar.distance (sourceCoefficient 36 97 3 2) v2922_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2922_upper : Scalar.QComplex := ((999993210041999737934383586382 : Int)/10^30,(-3685087501945440360128957634 : Int)/10^30)
theorem v2922_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 97 5) 1) 14) v2922_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2922 : Material (36 : Basis) (97 : Basis) where
  plus := ![v2922_pa,v2922_pb,v2922_pg]
  minus := ![(Primitive.Addresses.material2922 1).one,v2922_mb,v2922_mg]
  upper := v2922_upper
  lower := (Primitive.Addresses.material2922 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2922_pa_checked.trans (by decide +kernel)
    · exact v2922_pb_checked.trans (by decide +kernel)
    · exact v2922_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 97 Primitive.Addresses.material2922
    · exact v2922_mb_checked.trans (by decide +kernel)
    · exact v2922_mg_checked.trans (by decide +kernel)
  upper_error := v2922_upper_checked
  lower_error := reuse_lower_error 36 97 Primitive.Addresses.material2922

def v2923_pa : Scalar.QComplex := ((999999668558544338844725285465 : Int)/10^30,(-814176148919183224339934075 : Int)/10^30)
theorem v2923_pa_checked : Scalar.distance (sourceCoefficient 37 38 1 0) v2923_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2923_pb : Scalar.QComplex := ((-351298706361718533955165 : Int)/10^30,(-431477377952070831299641814 : Int)/10^30)
theorem v2923_pb_checked : Scalar.distance (sourceCoefficient 37 38 1 1) v2923_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2923_pg : Scalar.QComplex := ((-93086399040062549429190 : Int)/10^30,(75788751006726436995 : Int)/10^30)
theorem v2923_pg_checked : Scalar.distance (sourceCoefficient 37 38 1 2) v2923_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2923_mb : Scalar.QComplex := ((-723644119710076778561802 : Int)/10^30,(-431476914138361845643337868 : Int)/10^30)
theorem v2923_mb_checked : Scalar.distance (sourceCoefficient 37 38 3 1) v2923_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2923_mg : Scalar.QComplex := ((-93086298977463208042247 : Int)/10^30,(156118092702903210020 : Int)/10^30)
theorem v2923_mg_checked : Scalar.distance (sourceCoefficient 37 38 3 2) v2923_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2923_upper : Scalar.QComplex := ((999996773982334682399165421360 : Int)/10^30,(-2540083644970225134639682823 : Int)/10^30)
theorem v2923_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 38 5) 1) 14) v2923_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2923 : Material (37 : Basis) (38 : Basis) where
  plus := ![v2923_pa,v2923_pb,v2923_pg]
  minus := ![(Primitive.Addresses.material2923 1).one,v2923_mb,v2923_mg]
  upper := v2923_upper
  lower := (Primitive.Addresses.material2923 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2923_pa_checked.trans (by decide +kernel)
    · exact v2923_pb_checked.trans (by decide +kernel)
    · exact v2923_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 38 Primitive.Addresses.material2923
    · exact v2923_mb_checked.trans (by decide +kernel)
    · exact v2923_mg_checked.trans (by decide +kernel)
  upper_error := v2923_upper_checked
  lower_error := reuse_lower_error 37 38 Primitive.Addresses.material2923

def v2924_pa : Scalar.QComplex := ((999999657461644863471820571858 : Int)/10^30,(-827693538056527066431432526 : Int)/10^30)
theorem v2924_pa_checked : Scalar.distance (sourceCoefficient 37 39 1 0) v2924_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2924_pb : Scalar.QComplex := ((-357131155868202117600336 : Int)/10^30,(-431477373105567568616346047 : Int)/10^30)
theorem v2924_pb_checked : Scalar.distance (sourceCoefficient 37 39 1 1) v2924_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2924_pg : Scalar.QComplex := ((-93086398000787844285289 : Int)/10^30,(77047036497775268720 : Int)/10^30)
theorem v2924_pg_checked : Scalar.distance (sourceCoefficient 37 39 1 2) v2924_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2924_mb : Scalar.QComplex := ((-729476562862558817540942 : Int)/10^30,(-431476904258719147213862202 : Int)/10^30)
theorem v2924_mb_checked : Scalar.distance (sourceCoefficient 37 39 3 1) v2924_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2924_mg : Scalar.QComplex := ((-93086296852345182167463 : Int)/10^30,(157376376828587583595 : Int)/10^30)
theorem v2924_mg_checked : Scalar.distance (sourceCoefficient 37 39 3 2) v2924_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2924_upper : Scalar.QComplex := ((999996739555664371462328402244 : Int)/10^30,(-2553600994822763929089809271 : Int)/10^30)
theorem v2924_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 39 5) 1) 14) v2924_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2924 : Material (37 : Basis) (39 : Basis) where
  plus := ![v2924_pa,v2924_pb,v2924_pg]
  minus := ![(Primitive.Addresses.material2924 1).one,v2924_mb,v2924_mg]
  upper := v2924_upper
  lower := (Primitive.Addresses.material2924 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2924_pa_checked.trans (by decide +kernel)
    · exact v2924_pb_checked.trans (by decide +kernel)
    · exact v2924_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 39 Primitive.Addresses.material2924
    · exact v2924_mb_checked.trans (by decide +kernel)
    · exact v2924_mg_checked.trans (by decide +kernel)
  upper_error := v2924_upper_checked
  lower_error := reuse_lower_error 37 39 Primitive.Addresses.material2924

def v2925_pa : Scalar.QComplex := ((999999638385168188598956444288 : Int)/10^30,(-850429028701111249363422618 : Int)/10^30)
theorem v2925_pa_checked : Scalar.distance (sourceCoefficient 37 40 1 0) v2925_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2925_pb : Scalar.QComplex := ((-366941008874045393347578 : Int)/10^30,(-431477364716930323790771970 : Int)/10^30)
theorem v2925_pb_checked : Scalar.distance (sourceCoefficient 37 40 1 1) v2925_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2925_pg : Scalar.QComplex := ((-93086396208030147245028 : Int)/10^30,(79163402139142233625 : Int)/10^30)
theorem v2925_pg_checked : Scalar.distance (sourceCoefficient 37 40 1 2) v2925_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2925_mb : Scalar.QComplex := ((-739286404976729354694357 : Int)/10^30,(-431476887404623701196843984 : Int)/10^30)
theorem v2925_mb_checked : Scalar.distance (sourceCoefficient 37 40 3 1) v2925_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2925_mg : Scalar.QComplex := ((-93086293233259921723267 : Int)/10^30,(159492740134865747795 : Int)/10^30)
theorem v2925_mg_checked : Scalar.distance (sourceCoefficient 37 40 3 2) v2925_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2925_upper : Scalar.QComplex := ((999996681239821803807830409419 : Int)/10^30,(-2576336418681237358865738565 : Int)/10^30)
theorem v2925_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 40 5) 1) 14) v2925_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2925 : Material (37 : Basis) (40 : Basis) where
  plus := ![v2925_pa,v2925_pb,v2925_pg]
  minus := ![(Primitive.Addresses.material2925 1).one,v2925_mb,v2925_mg]
  upper := v2925_upper
  lower := (Primitive.Addresses.material2925 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2925_pa_checked.trans (by decide +kernel)
    · exact v2925_pb_checked.trans (by decide +kernel)
    · exact v2925_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 40 Primitive.Addresses.material2925
    · exact v2925_mb_checked.trans (by decide +kernel)
    · exact v2925_mg_checked.trans (by decide +kernel)
  upper_error := v2925_upper_checked
  lower_error := reuse_lower_error 37 40 Primitive.Addresses.material2925

def v2926_pa : Scalar.QComplex := ((999999625962665927307877450068 : Int)/10^30,(-864913017731527130755416378 : Int)/10^30)
theorem v2926_pa_checked : Scalar.distance (sourceCoefficient 37 41 1 0) v2926_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2926_pb : Scalar.QComplex := ((-373190524431045322478908 : Int)/10^30,(-431477359217752492822466510 : Int)/10^30)
theorem v2926_pb_checked : Scalar.distance (sourceCoefficient 37 41 1 1) v2926_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2926_pg : Scalar.QComplex := ((-93086395036654022316046 : Int)/10^30,(80511664955270001123 : Int)/10^30)
theorem v2926_pg_checked : Scalar.distance (sourceCoefficient 37 41 1 2) v2926_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2926_mb : Scalar.QComplex := ((-745535913461206230633669 : Int)/10^30,(-431476876512397459864944917 : Int)/10^30)
theorem v2926_mb_checked : Scalar.distance (sourceCoefficient 37 41 3 1) v2926_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2926_mg : Scalar.QComplex := ((-93086290898394146135964 : Int)/10^30,(160841001438128811202 : Int)/10^30)
theorem v2926_mg_checked : Scalar.distance (sourceCoefficient 37 41 3 2) v2926_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2926_upper : Scalar.QComplex := ((999996643819286955097421268959 : Int)/10^30,(-2590820364699341045935652900 : Int)/10^30)
theorem v2926_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 41 5) 1) 14) v2926_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2926 : Material (37 : Basis) (41 : Basis) where
  plus := ![v2926_pa,v2926_pb,v2926_pg]
  minus := ![(Primitive.Addresses.material2926 1).one,v2926_mb,v2926_mg]
  upper := v2926_upper
  lower := (Primitive.Addresses.material2926 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2926_pa_checked.trans (by decide +kernel)
    · exact v2926_pb_checked.trans (by decide +kernel)
    · exact v2926_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 41 Primitive.Addresses.material2926
    · exact v2926_mb_checked.trans (by decide +kernel)
    · exact v2926_mg_checked.trans (by decide +kernel)
  upper_error := v2926_upper_checked
  lower_error := reuse_lower_error 37 41 Primitive.Addresses.material2926

def v2927_pa : Scalar.QComplex := ((999999615789071183177000025707 : Int)/10^30,(-876596663246905234113236432 : Int)/10^30)
theorem v2927_pa_checked : Scalar.distance (sourceCoefficient 37 42 1 0) v2927_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2927_pb : Scalar.QComplex := ((-378231754711999148921513 : Int)/10^30,(-431477354693844352145688685 : Int)/10^30)
theorem v2927_pb_checked : Scalar.distance (sourceCoefficient 37 42 1 1) v2927_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2927_pg : Scalar.QComplex := ((-93086394075151025316691 : Int)/10^30,(81599253791288967846 : Int)/10^30)
theorem v2927_pg_checked : Scalar.distance (sourceCoefficient 37 42 1 2) v2927_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2927_mb : Scalar.QComplex := ((-750577137961150651726621 : Int)/10^30,(-431476867638136319766183024 : Int)/10^30)
theorem v2927_mb_checked : Scalar.distance (sourceCoefficient 37 42 3 1) v2927_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2927_mg : Scalar.QComplex := ((-93086288998351324846582 : Int)/10^30,(161928589039454967088 : Int)/10^30)
theorem v2927_mg_checked : Scalar.distance (sourceCoefficient 37 42 3 2) v2927_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2927_upper : Scalar.QComplex := ((999996613480795135839654816382 : Int)/10^30,(-2602503975254600024485570470 : Int)/10^30)
theorem v2927_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 42 5) 1) 14) v2927_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2927 : Material (37 : Basis) (42 : Basis) where
  plus := ![v2927_pa,v2927_pb,v2927_pg]
  minus := ![(Primitive.Addresses.material2927 1).one,v2927_mb,v2927_mg]
  upper := v2927_upper
  lower := (Primitive.Addresses.material2927 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2927_pa_checked.trans (by decide +kernel)
    · exact v2927_pb_checked.trans (by decide +kernel)
    · exact v2927_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 42 Primitive.Addresses.material2927
    · exact v2927_mb_checked.trans (by decide +kernel)
    · exact v2927_mg_checked.trans (by decide +kernel)
  upper_error := v2927_upper_checked
  lower_error := reuse_lower_error 37 42 Primitive.Addresses.material2927

def v2928_pa : Scalar.QComplex := ((999999602101512510730617219905 : Int)/10^30,(-892074445691239616125375483 : Int)/10^30)
theorem v2928_pa_checked : Scalar.distance (sourceCoefficient 37 43 1 0) v2928_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2928_pb : Scalar.QComplex := ((-384910069717890416863119 : Int)/10^30,(-431477348579917699498852846 : Int)/10^30)
theorem v2928_pb_checked : Scalar.distance (sourceCoefficient 37 43 1 1) v2928_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2928_pg : Scalar.QComplex := ((-93086392778582530495833 : Int)/10^30,(83040025280851481511 : Int)/10^30)
theorem v2928_pg_checked : Scalar.distance (sourceCoefficient 37 43 1 2) v2928_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2928_mb : Scalar.QComplex := ((-757255445204356688701591 : Int)/10^30,(-431476855761126873671877602 : Int)/10^30)
theorem v2928_mb_checked : Scalar.distance (sourceCoefficient 37 43 3 1) v2928_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2928_mg : Scalar.QComplex := ((-93086286458462407244043 : Int)/10^30,(163369358873672192925 : Int)/10^30)
theorem v2928_mg_checked : Scalar.distance (sourceCoefficient 37 43 3 2) v2928_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2928_upper : Scalar.QComplex := ((999996573080008483937779078064 : Int)/10^30,(-2617981711023111060685972543 : Int)/10^30)
theorem v2928_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 43 5) 1) 14) v2928_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2928 : Material (37 : Basis) (43 : Basis) where
  plus := ![v2928_pa,v2928_pb,v2928_pg]
  minus := ![(Primitive.Addresses.material2928 1).one,v2928_mb,v2928_mg]
  upper := v2928_upper
  lower := (Primitive.Addresses.material2928 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2928_pa_checked.trans (by decide +kernel)
    · exact v2928_pb_checked.trans (by decide +kernel)
    · exact v2928_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 43 Primitive.Addresses.material2928
    · exact v2928_mb_checked.trans (by decide +kernel)
    · exact v2928_mg_checked.trans (by decide +kernel)
  upper_error := v2928_upper_checked
  lower_error := reuse_lower_error 37 43 Primitive.Addresses.material2928

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
