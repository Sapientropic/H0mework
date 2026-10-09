import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B122

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2929_pa : Scalar.QComplex := ((999999596860576256181897514045 : Int)/10^30,(-897930222771369483919189936 : Int)/10^30)
theorem v2929_pa_checked : Scalar.distance (sourceCoefficient 37 44 1 0) v2929_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2929_pb : Scalar.QComplex := ((-387436705812898609130416 : Int)/10^30,(-431477346230874310220464118 : Int)/10^30)
theorem v2929_pb_checked : Scalar.distance (sourceCoefficient 37 44 1 1) v2929_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2929_pg : Scalar.QComplex := ((-93086392281262641577903 : Int)/10^30,(83585118654553820522 : Int)/10^30)
theorem v2929_pg_checked : Scalar.distance (sourceCoefficient 37 44 1 2) v2929_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2929_mb : Scalar.QComplex := ((-759782078331464141862950 : Int)/10^30,(-431476851231711204523062290 : Int)/10^30)
theorem v2929_mb_checked : Scalar.distance (sourceCoefficient 37 44 3 1) v2929_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2929_mg : Scalar.QComplex := ((-93086285490751672090127 : Int)/10^30,(163914451615246691229 : Int)/10^30)
theorem v2929_mg_checked : Scalar.distance (sourceCoefficient 37 44 3 2) v2929_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2929_upper : Scalar.QComplex := ((999996557732540026790768235288 : Int)/10^30,(-2623837470336368314194144650 : Int)/10^30)
theorem v2929_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 44 5) 1) 14) v2929_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2929 : Material (37 : Basis) (44 : Basis) where
  plus := ![v2929_pa,v2929_pb,v2929_pg]
  minus := ![(Primitive.Addresses.material2929 1).one,v2929_mb,v2929_mg]
  upper := v2929_upper
  lower := (Primitive.Addresses.material2929 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2929_pa_checked.trans (by decide +kernel)
    · exact v2929_pb_checked.trans (by decide +kernel)
    · exact v2929_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 44 Primitive.Addresses.material2929
    · exact v2929_mb_checked.trans (by decide +kernel)
    · exact v2929_mg_checked.trans (by decide +kernel)
  upper_error := v2929_upper_checked
  lower_error := reuse_lower_error 37 44 Primitive.Addresses.material2929

def v2930_pa : Scalar.QComplex := ((999999594240371364116594245533 : Int)/10^30,(-900843545034813789878301526 : Int)/10^30)
theorem v2930_pa_checked : Scalar.distance (sourceCoefficient 37 45 1 0) v2930_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2930_pb : Scalar.QComplex := ((-388693738837645227478366 : Int)/10^30,(-431477345054847167711459449 : Int)/10^30)
theorem v2930_pb_checked : Scalar.distance (sourceCoefficient 37 45 1 1) v2930_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2930_pg : Scalar.QComplex := ((-93086392032452557196993 : Int)/10^30,(83856309418519975197 : Int)/10^30)
theorem v2930_pg_checked : Scalar.distance (sourceCoefficient 37 45 1 2) v2930_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2930_mb : Scalar.QComplex := ((-761039109873301458161479 : Int)/10^30,(-431476848970921614212177643 : Int)/10^30)
theorem v2930_mb_checked : Scalar.distance (sourceCoefficient 37 45 3 1) v2930_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2930_mg : Scalar.QComplex := ((-93086285007916265028396 : Int)/10^30,(164185642063524233618 : Int)/10^30)
theorem v2930_mg_checked : Scalar.distance (sourceCoefficient 37 45 3 2) v2930_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2930_upper : Scalar.QComplex := ((999996550084209105039172814181 : Int)/10^30,(-2626750783738525391052132100 : Int)/10^30)
theorem v2930_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 45 5) 1) 14) v2930_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2930 : Material (37 : Basis) (45 : Basis) where
  plus := ![v2930_pa,v2930_pb,v2930_pg]
  minus := ![(Primitive.Addresses.material2930 1).one,v2930_mb,v2930_mg]
  upper := v2930_upper
  lower := (Primitive.Addresses.material2930 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2930_pa_checked.trans (by decide +kernel)
    · exact v2930_pb_checked.trans (by decide +kernel)
    · exact v2930_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 45 Primitive.Addresses.material2930
    · exact v2930_mb_checked.trans (by decide +kernel)
    · exact v2930_mg_checked.trans (by decide +kernel)
  upper_error := v2930_upper_checked
  lower_error := reuse_lower_error 37 45 Primitive.Addresses.material2930

def v2931_pa : Scalar.QComplex := ((999999579364854301560326327264 : Int)/10^30,(-917207781510249481484471045 : Int)/10^30)
theorem v2931_pa_checked : Scalar.distance (sourceCoefficient 37 46 1 0) v2931_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2931_pb : Scalar.QComplex := ((-395754538755847070869465 : Int)/10^30,(-431477338358316775242567176 : Int)/10^30)
theorem v2931_pb_checked : Scalar.distance (sourceCoefficient 37 46 1 1) v2931_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2931_pg : Scalar.QComplex := ((-93086390617747552467213 : Int)/10^30,(85379597740960269806 : Int)/10^30)
theorem v2931_pg_checked : Scalar.distance (sourceCoefficient 37 46 1 2) v2931_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2931_mb : Scalar.QComplex := ((-768099901383640669340623 : Int)/10^30,(-431476836181241392382761254 : Int)/10^30)
theorem v2931_mb_checked : Scalar.distance (sourceCoefficient 37 46 3 1) v2931_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2931_mg : Scalar.QComplex := ((-93086282278682571151226 : Int)/10^30,(165708928597947964934 : Int)/10^30)
theorem v2931_mg_checked : Scalar.distance (sourceCoefficient 37 46 3 2) v2931_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2931_upper : Scalar.QComplex := ((999996506965526593152533085191 : Int)/10^30,(-2643114970167560177140035339 : Int)/10^30)
theorem v2931_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 46 5) 1) 14) v2931_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2931 : Material (37 : Basis) (46 : Basis) where
  plus := ![v2931_pa,v2931_pb,v2931_pg]
  minus := ![(Primitive.Addresses.material2931 1).one,v2931_mb,v2931_mg]
  upper := v2931_upper
  lower := (Primitive.Addresses.material2931 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2931_pa_checked.trans (by decide +kernel)
    · exact v2931_pb_checked.trans (by decide +kernel)
    · exact v2931_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 46 Primitive.Addresses.material2931
    · exact v2931_mb_checked.trans (by decide +kernel)
    · exact v2931_mg_checked.trans (by decide +kernel)
  upper_error := v2931_upper_checked
  lower_error := reuse_lower_error 37 46 Primitive.Addresses.material2931

def v2932_pa : Scalar.QComplex := ((999999575745096803079170711270 : Int)/10^30,(-921145822550164297247453450 : Int)/10^30)
theorem v2932_pa_checked : Scalar.distance (sourceCoefficient 37 47 1 0) v2932_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2932_pb : Scalar.QComplex := ((-397453714869889715353492 : Int)/10^30,(-431477336723803717404261206 : Int)/10^30)
theorem v2932_pb_checked : Scalar.distance (sourceCoefficient 37 47 1 1) v2932_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2932_pg : Scalar.QComplex := ((-93086390272958482456636 : Int)/10^30,(85746175914445516271 : Int)/10^30)
theorem v2932_pg_checked : Scalar.distance (sourceCoefficient 37 47 1 2) v2932_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2932_mb : Scalar.QComplex := ((-769799075454491237202791 : Int)/10^30,(-431476833080416484780887144 : Int)/10^30)
theorem v2932_mb_checked : Scalar.distance (sourceCoefficient 37 47 3 1) v2932_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2932_mg : Scalar.QComplex := ((-93086281617553175871660 : Int)/10^30,(166075506337401965265 : Int)/10^30)
theorem v2932_mg_checked : Scalar.distance (sourceCoefficient 37 47 3 2) v2932_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2932_upper : Scalar.QComplex := ((999996496549072907274400931797 : Int)/10^30,(-2647052999094852398202569623 : Int)/10^30)
theorem v2932_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 47 5) 1) 14) v2932_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2932 : Material (37 : Basis) (47 : Basis) where
  plus := ![v2932_pa,v2932_pb,v2932_pg]
  minus := ![(Primitive.Addresses.material2932 1).one,v2932_mb,v2932_mg]
  upper := v2932_upper
  lower := (Primitive.Addresses.material2932 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2932_pa_checked.trans (by decide +kernel)
    · exact v2932_pb_checked.trans (by decide +kernel)
    · exact v2932_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 47 Primitive.Addresses.material2932
    · exact v2932_mb_checked.trans (by decide +kernel)
    · exact v2932_mg_checked.trans (by decide +kernel)
  upper_error := v2932_upper_checked
  lower_error := reuse_lower_error 37 47 Primitive.Addresses.material2932

def v2933_pa : Scalar.QComplex := ((999999550101325979832016023983 : Int)/10^30,(-948576378385799296542158753 : Int)/10^30)
theorem v2933_pa_checked : Scalar.distance (sourceCoefficient 37 48 1 0) v2933_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2933_pb : Scalar.QComplex := ((-409289382529197767832543 : Int)/10^30,(-431477325091036189517198227 : Int)/10^30)
theorem v2933_pb_checked : Scalar.distance (sourceCoefficient 37 48 1 1) v2933_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2933_pg : Scalar.QComplex := ((-93086387824595463237411 : Int)/10^30,(88299588365538448956 : Int)/10^30)
theorem v2933_pg_checked : Scalar.distance (sourceCoefficient 37 48 1 2) v2933_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2933_mb : Scalar.QComplex := ((-781634728668284847221676 : Int)/10^30,(-431476811234005157005276012 : Int)/10^30)
theorem v2933_mb_checked : Scalar.distance (sourceCoefficient 37 48 3 1) v2933_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2933_mg : Scalar.QComplex := ((-93086276965711124424426 : Int)/10^30,(168628915724915730284 : Int)/10^30)
theorem v2933_mg_checked : Scalar.distance (sourceCoefficient 37 48 3 2) v2933_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2933_upper : Scalar.QComplex := ((999996423562689385692015006641 : Int)/10^30,(-2674483469817074643547743104 : Int)/10^30)
theorem v2933_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 48 5) 1) 14) v2933_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2933 : Material (37 : Basis) (48 : Basis) where
  plus := ![v2933_pa,v2933_pb,v2933_pg]
  minus := ![(Primitive.Addresses.material2933 1).one,v2933_mb,v2933_mg]
  upper := v2933_upper
  lower := (Primitive.Addresses.material2933 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2933_pa_checked.trans (by decide +kernel)
    · exact v2933_pb_checked.trans (by decide +kernel)
    · exact v2933_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 48 Primitive.Addresses.material2933
    · exact v2933_mb_checked.trans (by decide +kernel)
    · exact v2933_mg_checked.trans (by decide +kernel)
  upper_error := v2933_upper_checked
  lower_error := reuse_lower_error 37 48 Primitive.Addresses.material2933

def v2934_pa : Scalar.QComplex := ((999999528953390362281578169822 : Int)/10^30,(-970614752304192207650859135 : Int)/10^30)
theorem v2934_pa_checked : Scalar.distance (sourceCoefficient 37 49 1 0) v2934_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2934_pb : Scalar.QComplex := ((-418798444915900268357456 : Int)/10^30,(-431477315431386140771865930 : Int)/10^30)
theorem v2934_pb_checked : Scalar.distance (sourceCoefficient 37 49 1 1) v2934_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2934_pg : Scalar.QComplex := ((-93086385798322037866255 : Int)/10^30,(90351061854092183536 : Int)/10^30)
theorem v2934_pg_checked : Scalar.distance (sourceCoefficient 37 49 1 2) v2934_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2934_mb : Scalar.QComplex := ((-791143779178485897978203 : Int)/10^30,(-431476793368466137536549779 : Int)/10^30)
theorem v2934_mb_checked : Scalar.distance (sourceCoefficient 37 49 3 1) v2934_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2934_mg : Scalar.QComplex := ((-93086273169109227841662 : Int)/10^30,(170680386701029421977 : Int)/10^30)
theorem v2934_mg_checked : Scalar.distance (sourceCoefficient 37 49 3 2) v2934_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2934_upper : Scalar.QComplex := ((999996364378551188025461728070 : Int)/10^30,(-2696521774412480062305056221 : Int)/10^30)
theorem v2934_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 49 5) 1) 14) v2934_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2934 : Material (37 : Basis) (49 : Basis) where
  plus := ![v2934_pa,v2934_pb,v2934_pg]
  minus := ![(Primitive.Addresses.material2934 1).one,v2934_mb,v2934_mg]
  upper := v2934_upper
  lower := (Primitive.Addresses.material2934 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2934_pa_checked.trans (by decide +kernel)
    · exact v2934_pb_checked.trans (by decide +kernel)
    · exact v2934_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 49 Primitive.Addresses.material2934
    · exact v2934_mb_checked.trans (by decide +kernel)
    · exact v2934_mg_checked.trans (by decide +kernel)
  upper_error := v2934_upper_checked
  lower_error := reuse_lower_error 37 49 Primitive.Addresses.material2934

def v2935_pa : Scalar.QComplex := ((999999526450468500260593521614 : Int)/10^30,(-973190032188123076305150840 : Int)/10^30)
theorem v2935_pa_checked : Scalar.distance (sourceCoefficient 37 50 1 0) v2935_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2935_pb : Scalar.QComplex := ((-419909620224865174066409 : Int)/10^30,(-431477314284380591178255198 : Int)/10^30)
theorem v2935_pb_checked : Scalar.distance (sourceCoefficient 37 50 1 1) v2935_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2935_pg : Scalar.QComplex := ((-93086385558101224165566 : Int)/10^30,(90590785456788576674 : Int)/10^30)
theorem v2935_pg_checked : Scalar.distance (sourceCoefficient 37 50 1 2) v2935_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2935_mb : Scalar.QComplex := ((-792254953083895322852147 : Int)/10^30,(-431476791262566768866952583 : Int)/10^30)
theorem v2935_mb_checked : Scalar.distance (sourceCoefficient 37 50 3 1) v2935_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2935_mg : Scalar.QComplex := ((-93086272722017831209444 : Int)/10^30,(170920110007166018842 : Int)/10^30)
theorem v2935_mg_checked : Scalar.distance (sourceCoefficient 37 50 3 2) v2935_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2935_upper : Scalar.QComplex := ((999996357430933601713969222780 : Int)/10^30,(-2699097046141017986919290653 : Int)/10^30)
theorem v2935_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 50 5) 1) 14) v2935_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2935 : Material (37 : Basis) (50 : Basis) where
  plus := ![v2935_pa,v2935_pb,v2935_pg]
  minus := ![(Primitive.Addresses.material2935 1).one,v2935_mb,v2935_mg]
  upper := v2935_upper
  lower := (Primitive.Addresses.material2935 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2935_pa_checked.trans (by decide +kernel)
    · exact v2935_pb_checked.trans (by decide +kernel)
    · exact v2935_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 50 Primitive.Addresses.material2935
    · exact v2935_mb_checked.trans (by decide +kernel)
    · exact v2935_mg_checked.trans (by decide +kernel)
  upper_error := v2935_upper_checked
  lower_error := reuse_lower_error 37 50 Primitive.Addresses.material2935

def v2936_pa : Scalar.QComplex := ((999999515390314030942196621062 : Int)/10^30,(-984489277286232240316787275 : Int)/10^30)
theorem v2936_pa_checked : Scalar.distance (sourceCoefficient 37 51 1 0) v2936_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2936_pb : Scalar.QComplex := ((-424784990161239751955930 : Int)/10^30,(-431477309206706929615577705 : Int)/10^30)
theorem v2936_pb_checked : Scalar.distance (sourceCoefficient 37 51 1 1) v2936_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2936_pg : Scalar.QComplex := ((-93086384495600541126232 : Int)/10^30,(91642591808149748329 : Int)/10^30)
theorem v2936_pg_checked : Scalar.distance (sourceCoefficient 37 51 1 2) v2936_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2936_mb : Scalar.QComplex := ((-797130316823143178019772 : Int)/10^30,(-431476781977670321373776564 : Int)/10^30)
theorem v2936_mb_checked : Scalar.distance (sourceCoefficient 37 51 3 1) v2936_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2936_mg : Scalar.QComplex := ((-93086270751856034162531 : Int)/10^30,(171971915050001379752 : Int)/10^30)
theorem v2936_mg_checked : Scalar.distance (sourceCoefficient 37 51 3 2) v2936_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2936_upper : Scalar.QComplex := ((999996326869323625367995295108 : Int)/10^30,(-2710396255321405635196483285 : Int)/10^30)
theorem v2936_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 51 5) 1) 14) v2936_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2936 : Material (37 : Basis) (51 : Basis) where
  plus := ![v2936_pa,v2936_pb,v2936_pg]
  minus := ![(Primitive.Addresses.material2936 1).one,v2936_mb,v2936_mg]
  upper := v2936_upper
  lower := (Primitive.Addresses.material2936 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2936_pa_checked.trans (by decide +kernel)
    · exact v2936_pb_checked.trans (by decide +kernel)
    · exact v2936_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 51 Primitive.Addresses.material2936
    · exact v2936_mb_checked.trans (by decide +kernel)
    · exact v2936_mg_checked.trans (by decide +kernel)
  upper_error := v2936_upper_checked
  lower_error := reuse_lower_error 37 51 Primitive.Addresses.material2936

def v2937_pa : Scalar.QComplex := ((999999491284017663278200856472 : Int)/10^30,(-1008678197385812891880302452 : Int)/10^30)
theorem v2937_pa_checked : Scalar.distance (sourceCoefficient 37 52 1 0) v2937_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2937_pb : Scalar.QComplex := ((-435221964654412328627233 : Int)/10^30,(-431477298089723199185156919 : Int)/10^30)
theorem v2937_pb_checked : Scalar.distance (sourceCoefficient 37 52 1 1) v2937_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2937_pg : Scalar.QComplex := ((-93086382174433807216958 : Int)/10^30,(93894251938381369066 : Int)/10^30)
theorem v2937_pg_checked : Scalar.distance (sourceCoefficient 37 52 1 2) v2937_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2937_mb : Scalar.QComplex := ((-807567277836696888583905 : Int)/10^30,(-431476761854051806578117189 : Int)/10^30)
theorem v2937_mb_checked : Scalar.distance (sourceCoefficient 37 52 3 1) v2937_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2937_mg : Scalar.QComplex := ((-93086266487608883147538 : Int)/10^30,(174223572338774678157 : Int)/10^30)
theorem v2937_mg_checked : Scalar.distance (sourceCoefficient 37 52 3 2) v2937_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2937_upper : Scalar.QComplex := ((999996261015181471014218745283 : Int)/10^30,(-2734585097789150604124341246 : Int)/10^30)
theorem v2937_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 52 5) 1) 14) v2937_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2937 : Material (37 : Basis) (52 : Basis) where
  plus := ![v2937_pa,v2937_pb,v2937_pg]
  minus := ![(Primitive.Addresses.material2937 1).one,v2937_mb,v2937_mg]
  upper := v2937_upper
  lower := (Primitive.Addresses.material2937 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2937_pa_checked.trans (by decide +kernel)
    · exact v2937_pb_checked.trans (by decide +kernel)
    · exact v2937_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 52 Primitive.Addresses.material2937
    · exact v2937_mb_checked.trans (by decide +kernel)
    · exact v2937_mg_checked.trans (by decide +kernel)
  upper_error := v2937_upper_checked
  lower_error := reuse_lower_error 37 52 Primitive.Addresses.material2937

def v2938_pa : Scalar.QComplex := ((999999487542340159225319220055 : Int)/10^30,(-1012380885373037963344004965 : Int)/10^30)
theorem v2938_pa_checked : Scalar.distance (sourceCoefficient 37 53 1 0) v2938_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2938_pb : Scalar.QComplex := ((-436819591157124066885412 : Int)/10^30,(-431477296358298189360797285 : Int)/10^30)
theorem v2938_pb_checked : Scalar.distance (sourceCoefficient 37 53 1 1) v2938_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2938_pg : Scalar.QComplex := ((-93086381813516355522907 : Int)/10^30,(94238921929997745417 : Int)/10^30)
theorem v2938_pg_checked : Scalar.distance (sourceCoefficient 37 53 1 2) v2938_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2938_mb : Scalar.QComplex := ((-809164902250397461753557 : Int)/10^30,(-431476758743947724028796894 : Int)/10^30)
theorem v2938_mb_checked : Scalar.distance (sourceCoefficient 37 53 3 1) v2938_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2938_mg : Scalar.QComplex := ((-93086265829256886434784 : Int)/10^30,(174568241890599158739 : Int)/10^30)
theorem v2938_mg_checked : Scalar.distance (sourceCoefficient 37 53 3 2) v2938_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2938_upper : Scalar.QComplex := ((999996250883005979030231132246 : Int)/10^30,(-2738287773803860937237045814 : Int)/10^30)
theorem v2938_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 53 5) 1) 14) v2938_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2938 : Material (37 : Basis) (53 : Basis) where
  plus := ![v2938_pa,v2938_pb,v2938_pg]
  minus := ![(Primitive.Addresses.material2938 1).one,v2938_mb,v2938_mg]
  upper := v2938_upper
  lower := (Primitive.Addresses.material2938 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2938_pa_checked.trans (by decide +kernel)
    · exact v2938_pb_checked.trans (by decide +kernel)
    · exact v2938_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 53 Primitive.Addresses.material2938
    · exact v2938_mb_checked.trans (by decide +kernel)
    · exact v2938_mg_checked.trans (by decide +kernel)
  upper_error := v2938_upper_checked
  lower_error := reuse_lower_error 37 53 Primitive.Addresses.material2938

def v2939_pa : Scalar.QComplex := ((999999485634791666485562309089 : Int)/10^30,(-1014263354408243091880182605 : Int)/10^30)
theorem v2939_pa_checked : Scalar.distance (sourceCoefficient 37 54 1 0) v2939_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2939_pb : Scalar.QComplex := ((-437631834162066668666563 : Int)/10^30,(-431477295475006870194271296 : Int)/10^30)
theorem v2939_pb_checked : Scalar.distance (sourceCoefficient 37 54 1 1) v2939_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2939_pg : Scalar.QComplex := ((-93086381629452824436931 : Int)/10^30,(94414154244570796788 : Int)/10^30)
theorem v2939_pg_checked : Scalar.distance (sourceCoefficient 37 54 1 2) v2939_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2939_mb : Scalar.QComplex := ((-809977144190664244978948 : Int)/10^30,(-431476757159727602553484558 : Int)/10^30)
theorem v2939_mb_checked : Scalar.distance (sourceCoefficient 37 54 3 1) v2939_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2939_mg : Scalar.QComplex := ((-93086265493975828578007 : Int)/10^30,(174743473981086673468 : Int)/10^30)
theorem v2939_mg_checked : Scalar.distance (sourceCoefficient 37 54 3 2) v2939_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2939_upper : Scalar.QComplex := ((999996245726489548852668817516 : Int)/10^30,(-2740170236743093921160256507 : Int)/10^30)
theorem v2939_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 54 5) 1) 14) v2939_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2939 : Material (37 : Basis) (54 : Basis) where
  plus := ![v2939_pa,v2939_pb,v2939_pg]
  minus := ![(Primitive.Addresses.material2939 1).one,v2939_mb,v2939_mg]
  upper := v2939_upper
  lower := (Primitive.Addresses.material2939 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2939_pa_checked.trans (by decide +kernel)
    · exact v2939_pb_checked.trans (by decide +kernel)
    · exact v2939_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 54 Primitive.Addresses.material2939
    · exact v2939_mb_checked.trans (by decide +kernel)
    · exact v2939_mg_checked.trans (by decide +kernel)
  upper_error := v2939_upper_checked
  lower_error := reuse_lower_error 37 54 Primitive.Addresses.material2939

def v2940_pa : Scalar.QComplex := ((999999469954631579779023091461 : Int)/10^30,(-1029606942426258783862974919 : Int)/10^30)
theorem v2940_pa_checked : Scalar.distance (sourceCoefficient 37 55 1 0) v2940_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2940_pb : Scalar.QComplex := ((-444252246903271597111972 : Int)/10^30,(-431477288199465861433562915 : Int)/10^30)
theorem v2940_pb_checked : Scalar.distance (sourceCoefficient 37 55 1 1) v2940_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2940_pg : Scalar.QComplex := ((-93086380114839627381499 : Int)/10^30,(95842434012406771148 : Int)/10^30)
theorem v2940_pg_checked : Scalar.distance (sourceCoefficient 37 55 1 2) v2940_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2940_mb : Scalar.QComplex := ((-816597548188322729706893 : Int)/10^30,(-431476744171071279470536160 : Int)/10^30)
theorem v2940_mb_checked : Scalar.distance (sourceCoefficient 37 55 3 1) v2940_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2940_mg : Scalar.QComplex := ((-93086262746822083172644 : Int)/10^30,(176171751910065841240 : Int)/10^30)
theorem v2940_mg_checked : Scalar.distance (sourceCoefficient 37 55 3 2) v2940_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2940_upper : Scalar.QComplex := ((999996203564711856239177413357 : Int)/10^30,(-2755513774846103828123548193 : Int)/10^30)
theorem v2940_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 55 5) 1) 14) v2940_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2940 : Material (37 : Basis) (55 : Basis) where
  plus := ![v2940_pa,v2940_pb,v2940_pg]
  minus := ![(Primitive.Addresses.material2940 1).one,v2940_mb,v2940_mg]
  upper := v2940_upper
  lower := (Primitive.Addresses.material2940 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2940_pa_checked.trans (by decide +kernel)
    · exact v2940_pb_checked.trans (by decide +kernel)
    · exact v2940_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 55 Primitive.Addresses.material2940
    · exact v2940_mb_checked.trans (by decide +kernel)
    · exact v2940_mg_checked.trans (by decide +kernel)
  upper_error := v2940_upper_checked
  lower_error := reuse_lower_error 37 55 Primitive.Addresses.material2940

def v2941_pa : Scalar.QComplex := ((999999466198724916196834352445 : Int)/10^30,(-1033248404413868451535359787 : Int)/10^30)
theorem v2941_pa_checked : Scalar.distance (sourceCoefficient 37 56 1 0) v2941_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2941_pb : Scalar.QComplex := ((-445823455749403831988834 : Int)/10^30,(-431477286452890426407699208 : Int)/10^30)
theorem v2941_pb_checked : Scalar.distance (sourceCoefficient 37 56 1 1) v2941_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2941_pg : Scalar.QComplex := ((-93086379751625637806990 : Int)/10^30,(96181404692787086877 : Int)/10^30)
theorem v2941_pg_checked : Scalar.distance (sourceCoefficient 37 56 1 2) v2941_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2941_mb : Scalar.QComplex := ((-818168754942206165787250 : Int)/10^30,(-431476741068614025181934296 : Int)/10^30)
theorem v2941_mb_checked : Scalar.distance (sourceCoefficient 37 56 3 1) v2941_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2941_mg : Scalar.QComplex := ((-93086262091091798343809 : Int)/10^30,(176510722150794566487 : Int)/10^30)
theorem v2941_mg_checked : Scalar.distance (sourceCoefficient 37 56 3 2) v2941_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2941_upper : Scalar.QComplex := ((999996193523977746875434606492 : Int)/10^30,(-2759155224927829453272630786 : Int)/10^30)
theorem v2941_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 56 5) 1) 14) v2941_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2941 : Material (37 : Basis) (56 : Basis) where
  plus := ![v2941_pa,v2941_pb,v2941_pg]
  minus := ![(Primitive.Addresses.material2941 1).one,v2941_mb,v2941_mg]
  upper := v2941_upper
  lower := (Primitive.Addresses.material2941 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2941_pa_checked.trans (by decide +kernel)
    · exact v2941_pb_checked.trans (by decide +kernel)
    · exact v2941_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 56 Primitive.Addresses.material2941
    · exact v2941_mb_checked.trans (by decide +kernel)
    · exact v2941_mg_checked.trans (by decide +kernel)
  upper_error := v2941_upper_checked
  lower_error := reuse_lower_error 37 56 Primitive.Addresses.material2941

def v2942_pa : Scalar.QComplex := ((999999453959914717997152380085 : Int)/10^30,(-1045026254409060748963517114 : Int)/10^30)
theorem v2942_pa_checked : Scalar.distance (sourceCoefficient 37 57 1 0) v2942_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2942_pb : Scalar.QComplex := ((-450905332778809216513651 : Int)/10^30,(-431477280751572804253980043 : Int)/10^30)
theorem v2942_pb_checked : Scalar.distance (sourceCoefficient 37 57 1 1) v2942_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2942_pg : Scalar.QComplex := ((-93086378566994437232439 : Int)/10^30,(97277762647927880832 : Int)/10^30)
theorem v2942_pg_checked : Scalar.distance (sourceCoefficient 37 57 1 2) v2942_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2942_mb : Scalar.QComplex := ((-823250625159416148905657 : Int)/10^30,(-431476730981867528757489568 : Int)/10^30)
theorem v2942_mb_checked : Scalar.distance (sourceCoefficient 37 57 3 1) v2942_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2942_mg : Scalar.QComplex := ((-93086259960353501704386 : Int)/10^30,(177607078675427815421 : Int)/10^30)
theorem v2942_mg_checked : Scalar.distance (sourceCoefficient 37 57 3 2) v2942_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2942_upper : Scalar.QComplex := ((999996160957685163449036004114 : Int)/10^30,(-2770933036258221600404889582 : Int)/10^30)
theorem v2942_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 57 5) 1) 14) v2942_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2942 : Material (37 : Basis) (57 : Basis) where
  plus := ![v2942_pa,v2942_pb,v2942_pg]
  minus := ![(Primitive.Addresses.material2942 1).one,v2942_mb,v2942_mg]
  upper := v2942_upper
  lower := (Primitive.Addresses.material2942 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2942_pa_checked.trans (by decide +kernel)
    · exact v2942_pb_checked.trans (by decide +kernel)
    · exact v2942_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 57 Primitive.Addresses.material2942
    · exact v2942_mb_checked.trans (by decide +kernel)
    · exact v2942_mg_checked.trans (by decide +kernel)
  upper_error := v2942_upper_checked
  lower_error := reuse_lower_error 37 57 Primitive.Addresses.material2942

def v2943_pa : Scalar.QComplex := ((999999447261202329333456596867 : Int)/10^30,(-1051416801188355861814282487 : Int)/10^30)
theorem v2943_pa_checked : Scalar.distance (sourceCoefficient 37 58 1 0) v2943_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2943_pb : Scalar.QComplex := ((-453662709782597959485457 : Int)/10^30,(-431477277624695224701329935 : Int)/10^30)
theorem v2943_pb_checked : Scalar.distance (sourceCoefficient 37 58 1 1) v2943_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2943_pg : Scalar.QComplex := ((-93086377917920464506699 : Int)/10^30,(97872635802673378729 : Int)/10^30)
theorem v2943_pg_checked : Scalar.distance (sourceCoefficient 37 58 1 2) v2943_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2943_mb : Scalar.QComplex := ((-826007998438152893196823 : Int)/10^30,(-431476725475498946864770880 : Int)/10^30)
theorem v2943_mb_checked : Scalar.distance (sourceCoefficient 37 58 3 1) v2943_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2943_mg : Scalar.QComplex := ((-93086258797931030205507 : Int)/10^30,(178201951048553245505 : Int)/10^30)
theorem v2943_mg_checked : Scalar.distance (sourceCoefficient 37 58 3 2) v2943_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2943_upper : Scalar.QComplex := ((999996143229478756542283727784 : Int)/10^30,(-2777323561958178091460370553 : Int)/10^30)
theorem v2943_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 58 5) 1) 14) v2943_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2943 : Material (37 : Basis) (58 : Basis) where
  plus := ![v2943_pa,v2943_pb,v2943_pg]
  minus := ![(Primitive.Addresses.material2943 1).one,v2943_mb,v2943_mg]
  upper := v2943_upper
  lower := (Primitive.Addresses.material2943 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2943_pa_checked.trans (by decide +kernel)
    · exact v2943_pb_checked.trans (by decide +kernel)
    · exact v2943_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 58 Primitive.Addresses.material2943
    · exact v2943_mb_checked.trans (by decide +kernel)
    · exact v2943_mg_checked.trans (by decide +kernel)
  upper_error := v2943_upper_checked
  lower_error := reuse_lower_error 37 58 Primitive.Addresses.material2943

def v2944_pa : Scalar.QComplex := ((999999428637810719474528224201 : Int)/10^30,(-1068982718338467623384918622 : Int)/10^30)
theorem v2944_pa_checked : Scalar.distance (sourceCoefficient 37 59 1 0) v2944_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2944_pb : Scalar.QComplex := ((-461242007355512130503697 : Int)/10^30,(-431477268908689629500552171 : Int)/10^30)
theorem v2944_pb_checked : Scalar.distance (sourceCoefficient 37 59 1 1) v2944_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2944_pg : Scalar.QComplex := ((-93086376110937780674010 : Int)/10^30,(99507784230332711103 : Int)/10^30)
theorem v2944_pg_checked : Scalar.distance (sourceCoefficient 37 59 1 2) v2944_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2944_mb : Scalar.QComplex := ((-833587285667427912469407 : Int)/10^30,(-431476710218904150497134135 : Int)/10^30)
theorem v2944_mb_checked : Scalar.distance (sourceCoefficient 37 59 3 1) v2944_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2944_mg : Scalar.QComplex := ((-93086255579889570476425 : Int)/10^30,(179837097308027415618 : Int)/10^30)
theorem v2944_mg_checked : Scalar.distance (sourceCoefficient 37 59 3 2) v2944_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2944_upper : Scalar.QComplex := ((999996094288935450500192051612 : Int)/10^30,(-2794889420803635277789253382 : Int)/10^30)
theorem v2944_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 37 59 5) 1) 14) v2944_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2944 : Material (37 : Basis) (59 : Basis) where
  plus := ![v2944_pa,v2944_pb,v2944_pg]
  minus := ![(Primitive.Addresses.material2944 1).one,v2944_mb,v2944_mg]
  upper := v2944_upper
  lower := (Primitive.Addresses.material2944 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2944_pa_checked.trans (by decide +kernel)
    · exact v2944_pb_checked.trans (by decide +kernel)
    · exact v2944_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 37 59 Primitive.Addresses.material2944
    · exact v2944_mb_checked.trans (by decide +kernel)
    · exact v2944_mg_checked.trans (by decide +kernel)
  upper_error := v2944_upper_checked
  lower_error := reuse_lower_error 37 59 Primitive.Addresses.material2944

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
