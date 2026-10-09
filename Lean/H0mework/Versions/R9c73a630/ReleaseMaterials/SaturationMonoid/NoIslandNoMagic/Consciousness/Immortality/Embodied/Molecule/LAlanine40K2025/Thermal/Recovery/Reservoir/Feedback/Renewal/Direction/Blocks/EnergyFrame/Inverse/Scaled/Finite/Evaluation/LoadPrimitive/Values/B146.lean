import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B097
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B098

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2337_pa : Scalar.QComplex := ((999998330659225243073763174737 : Int)/10^30,(-1827205178083520593982470896 : Int)/10^30)
theorem v2337_pa_checked : Scalar.distance (sourceCoefficient 27 97 1 0) v2337_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2337_pb : Scalar.QComplex := ((-788397733697950628242645 : Int)/10^30,(-431476676538528204623361974 : Int)/10^30)
theorem v2337_pb_checked : Scalar.distance (sourceCoefficient 27 97 1 1) v2337_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2337_pg : Scalar.QComplex := ((-93086261108879036738878 : Int)/10^30,(170087982241382469196 : Int)/10^30)
theorem v2337_pg_checked : Scalar.distance (sourceCoefficient 27 97 1 2) v2337_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2337_mb : Scalar.QComplex := ((-1160742379006067789610055 : Int)/10^30,(-431475835528306005521642947 : Int)/10^30)
theorem v2337_mb_checked : Scalar.distance (sourceCoefficient 27 97 3 1) v2337_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2337_mg : Scalar.QComplex := ((-93086079670341577642967 : Int)/10^30,(250417169797246584234 : Int)/10^30)
theorem v2337_mg_checked : Scalar.distance (sourceCoefficient 27 97 3 2) v2337_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2337_upper : Scalar.QComplex := ((999993687688805168489422779681 : Int)/10^30,(-3553108856253970831785212583 : Int)/10^30)
theorem v2337_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 27 97 5) 1) 14) v2337_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2337 : Material (27 : Basis) (97 : Basis) where
  plus := ![v2337_pa,v2337_pb,v2337_pg]
  minus := ![(Primitive.Addresses.material2337 1).one,v2337_mb,v2337_mg]
  upper := v2337_upper
  lower := (Primitive.Addresses.material2337 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2337_pa_checked.trans (by decide +kernel)
    · exact v2337_pb_checked.trans (by decide +kernel)
    · exact v2337_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 27 97 Primitive.Addresses.material2337
    · exact v2337_mb_checked.trans (by decide +kernel)
    · exact v2337_mg_checked.trans (by decide +kernel)
  upper_error := v2337_upper_checked
  lower_error := reuse_lower_error 27 97 Primitive.Addresses.material2337

def v2338_pa : Scalar.QComplex := ((999999853937112932064083932075 : Int)/10^30,(-540486588919193122207810918 : Int)/10^30)
theorem v2338_pa_checked : Scalar.distance (sourceCoefficient 28 29 1 0) v2338_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2338_pb : Scalar.QComplex := ((-233207813513587380060335 : Int)/10^30,(-431477457964173830186852299 : Int)/10^30)
theorem v2338_pb_checked : Scalar.distance (sourceCoefficient 28 29 1 1) v2338_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2338_pg : Scalar.QComplex := ((-93086416299033478990929 : Int)/10^30,(50311966968887735933 : Int)/10^30)
theorem v2338_pg_checked : Scalar.distance (sourceCoefficient 28 29 1 2) v2338_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2338_mb : Scalar.QComplex := ((-605553339879423329140512 : Int)/10^30,(-431477096057556963927494608 : Int)/10^30)
theorem v2338_mb_checked : Scalar.distance (sourceCoefficient 28 29 3 1) v2338_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2338_mg : Scalar.QComplex := ((-93086338221744904196739 : Int)/10^30,(130641333044950149812 : Int)/10^30)
theorem v2338_mg_checked : Scalar.distance (sourceCoefficient 28 29 3 2) v2338_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2338_upper : Scalar.QComplex := ((999997431723978813069320108254 : Int)/10^30,(-2266394812545276797896799862 : Int)/10^30)
theorem v2338_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 29 5) 1) 14) v2338_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2338 : Material (28 : Basis) (29 : Basis) where
  plus := ![v2338_pa,v2338_pb,v2338_pg]
  minus := ![(Primitive.Addresses.material2338 1).one,v2338_mb,v2338_mg]
  upper := v2338_upper
  lower := (Primitive.Addresses.material2338 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2338_pa_checked.trans (by decide +kernel)
    · exact v2338_pb_checked.trans (by decide +kernel)
    · exact v2338_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 29 Primitive.Addresses.material2338
    · exact v2338_mb_checked.trans (by decide +kernel)
    · exact v2338_mg_checked.trans (by decide +kernel)
  upper_error := v2338_upper_checked
  lower_error := reuse_lower_error 28 29 Primitive.Addresses.material2338

def v2339_pa : Scalar.QComplex := ((999999851104169150230080155432 : Int)/10^30,(-545702885762546976148351537 : Int)/10^30)
theorem v2339_pa_checked : Scalar.distance (sourceCoefficient 28 30 1 0) v2339_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2339_pb : Scalar.QComplex := ((-235458528337586719172062 : Int)/10^30,(-431477456729538239068870195 : Int)/10^30)
theorem v2339_pb_checked : Scalar.distance (sourceCoefficient 28 30 1 1) v2339_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2339_pg : Scalar.QComplex := ((-93086416033999785381082 : Int)/10^30,(50797533418587649519 : Int)/10^30)
theorem v2339_pg_checked : Scalar.distance (sourceCoefficient 28 30 1 2) v2339_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2339_mb : Scalar.QComplex := ((-607804052799943767316323 : Int)/10^30,(-431477092880656307842038886 : Int)/10^30)
theorem v2339_mb_checked : Scalar.distance (sourceCoefficient 28 30 3 1) v2339_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2339_mg : Scalar.QComplex := ((-93086337537689332281098 : Int)/10^30,(131126899085139341780 : Int)/10^30)
theorem v2339_mg_checked : Scalar.distance (sourceCoefficient 28 30 3 2) v2339_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2339_upper : Scalar.QComplex := ((999997419888184117696593544086 : Int)/10^30,(-2271611096730165288139086904 : Int)/10^30)
theorem v2339_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 30 5) 1) 14) v2339_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2339 : Material (28 : Basis) (30 : Basis) where
  plus := ![v2339_pa,v2339_pb,v2339_pg]
  minus := ![(Primitive.Addresses.material2339 1).one,v2339_mb,v2339_mg]
  upper := v2339_upper
  lower := (Primitive.Addresses.material2339 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2339_pa_checked.trans (by decide +kernel)
    · exact v2339_pb_checked.trans (by decide +kernel)
    · exact v2339_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 30 Primitive.Addresses.material2339
    · exact v2339_mb_checked.trans (by decide +kernel)
    · exact v2339_mg_checked.trans (by decide +kernel)
  upper_error := v2339_upper_checked
  lower_error := reuse_lower_error 28 30 Primitive.Addresses.material2339

def v2340_pa : Scalar.QComplex := ((999999844988007438445183078428 : Int)/10^30,(-556797953565197468156075154 : Int)/10^30)
theorem v2340_pa_checked : Scalar.distance (sourceCoefficient 28 31 1 0) v2340_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2340_pb : Scalar.QComplex := ((-240245800666326490171173 : Int)/10^30,(-431477454051409308506391343 : Int)/10^30)
theorem v2340_pb_checked : Scalar.distance (sourceCoefficient 28 31 1 1) v2340_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2340_pg : Scalar.QComplex := ((-93086415460445834793391 : Int)/10^30,(51830333667419296535 : Int)/10^30)
theorem v2340_pg_checked : Scalar.distance (sourceCoefficient 28 31 1 2) v2340_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2340_mb : Scalar.QComplex := ((-612591321035058612545836 : Int)/10^30,(-431477086071327965508774528 : Int)/10^30)
theorem v2340_mb_checked : Scalar.distance (sourceCoefficient 28 31 3 1) v2340_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2340_mg : Scalar.QComplex := ((-93086336072875496108512 : Int)/10^30,(132159698454461027407 : Int)/10^30)
theorem v2340_mg_checked : Scalar.distance (sourceCoefficient 28 31 3 2) v2340_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2340_upper : Scalar.QComplex := ((999997394622951024529785473319 : Int)/10^30,(-2282706137452075345631593624 : Int)/10^30)
theorem v2340_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 31 5) 1) 14) v2340_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2340 : Material (28 : Basis) (31 : Basis) where
  plus := ![v2340_pa,v2340_pb,v2340_pg]
  minus := ![(Primitive.Addresses.material2340 1).one,v2340_mb,v2340_mg]
  upper := v2340_upper
  lower := (Primitive.Addresses.material2340 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2340_pa_checked.trans (by decide +kernel)
    · exact v2340_pb_checked.trans (by decide +kernel)
    · exact v2340_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 31 Primitive.Addresses.material2340
    · exact v2340_mb_checked.trans (by decide +kernel)
    · exact v2340_mg_checked.trans (by decide +kernel)
  upper_error := v2340_upper_checked
  lower_error := reuse_lower_error 28 31 Primitive.Addresses.material2340

def v2341_pa : Scalar.QComplex := ((999999842317284746761118602736 : Int)/10^30,(-561574042885387530409216726 : Int)/10^30)
theorem v2341_pa_checked : Scalar.distance (sourceCoefficient 28 32 1 0) v2341_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2341_pb : Scalar.QComplex := ((-242306575833445503055092 : Int)/10^30,(-431477452876751638553771112 : Int)/10^30)
theorem v2341_pb_checked : Scalar.distance (sourceCoefficient 28 32 1 1) v2341_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2341_pg : Scalar.QComplex := ((-93086415209432213747480 : Int)/10^30,(52274922769720438059 : Int)/10^30)
theorem v2341_pg_checked : Scalar.distance (sourceCoefficient 28 32 1 2) v2341_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2341_mb : Scalar.QComplex := ((-614652094421180184081951 : Int)/10^30,(-431477083118314577579295511 : Int)/10^30)
theorem v2341_mb_checked : Scalar.distance (sourceCoefficient 28 32 3 1) v2341_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2341_mg : Scalar.QComplex := ((-93086335438201596790418 : Int)/10^30,(132604287174607877690 : Int)/10^30)
theorem v2341_mg_checked : Scalar.distance (sourceCoefficient 28 32 3 2) v2341_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2341_upper : Scalar.QComplex := ((999997383709135427363900850372 : Int)/10^30,(-2287482215049416324547276930 : Int)/10^30)
theorem v2341_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 32 5) 1) 14) v2341_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2341 : Material (28 : Basis) (32 : Basis) where
  plus := ![v2341_pa,v2341_pb,v2341_pg]
  minus := ![(Primitive.Addresses.material2341 1).one,v2341_mb,v2341_mg]
  upper := v2341_upper
  lower := (Primitive.Addresses.material2341 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2341_pa_checked.trans (by decide +kernel)
    · exact v2341_pb_checked.trans (by decide +kernel)
    · exact v2341_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 32 Primitive.Addresses.material2341
    · exact v2341_mb_checked.trans (by decide +kernel)
    · exact v2341_mg_checked.trans (by decide +kernel)
  upper_error := v2341_upper_checked
  lower_error := reuse_lower_error 28 32 Primitive.Addresses.material2341

def v2342_pa : Scalar.QComplex := ((999999838557229934984465002787 : Int)/10^30,(-568230159412770930166847080 : Int)/10^30)
theorem v2342_pa_checked : Scalar.distance (sourceCoefficient 28 33 1 0) v2342_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2342_pb : Scalar.QComplex := ((-245178540470821331157374 : Int)/10^30,(-431477451217821136743393671 : Int)/10^30)
theorem v2342_pb_checked : Scalar.distance (sourceCoefficient 28 33 1 1) v2342_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2342_pg : Scalar.QComplex := ((-93086414855479361024188 : Int)/10^30,(52894516891929693666 : Int)/10^30)
theorem v2342_pg_checked : Scalar.distance (sourceCoefficient 28 33 1 2) v2342_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2342_mb : Scalar.QComplex := ((-617524056557610014815021 : Int)/10^30,(-431477078981008559894847029 : Int)/10^30)
theorem v2342_mb_checked : Scalar.distance (sourceCoefficient 28 33 3 1) v2342_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2342_mg : Scalar.QComplex := ((-93086334549567053876725 : Int)/10^30,(133223880760668554292 : Int)/10^30)
theorem v2342_mg_checked : Scalar.distance (sourceCoefficient 28 33 3 2) v2342_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2342_upper : Scalar.QComplex := ((999997368461232927657893605623 : Int)/10^30,(-2294138315173782543520299769 : Int)/10^30)
theorem v2342_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 33 5) 1) 14) v2342_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2342 : Material (28 : Basis) (33 : Basis) where
  plus := ![v2342_pa,v2342_pb,v2342_pg]
  minus := ![(Primitive.Addresses.material2342 1).one,v2342_mb,v2342_mg]
  upper := v2342_upper
  lower := (Primitive.Addresses.material2342 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2342_pa_checked.trans (by decide +kernel)
    · exact v2342_pb_checked.trans (by decide +kernel)
    · exact v2342_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 33 Primitive.Addresses.material2342
    · exact v2342_mb_checked.trans (by decide +kernel)
    · exact v2342_mg_checked.trans (by decide +kernel)
  upper_error := v2342_upper_checked
  lower_error := reuse_lower_error 28 33 Primitive.Addresses.material2342

def v2343_pa : Scalar.QComplex := ((999999829239987348424963795464 : Int)/10^30,(-584397121950620280125684664 : Int)/10^30)
theorem v2343_pa_checked : Scalar.distance (sourceCoefficient 28 34 1 0) v2343_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2343_pb : Scalar.QComplex := ((-252154221319370856415385 : Int)/10^30,(-431477447082326783328300105 : Int)/10^30)
theorem v2343_pb_checked : Scalar.distance (sourceCoefficient 28 34 1 1) v2343_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2343_pg : Scalar.QComplex := ((-93086413975731703011935 : Int)/10^30,(54399441709370958569 : Int)/10^30)
theorem v2343_pg_checked : Scalar.distance (sourceCoefficient 28 34 1 2) v2343_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2343_mb : Scalar.QComplex := ((-624499731240049384548324 : Int)/10^30,(-431477068825817347017830971 : Int)/10^30)
theorem v2343_mb_checked : Scalar.distance (sourceCoefficient 28 34 3 1) v2343_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2343_mg : Scalar.QComplex := ((-93086332371137385280613 : Int)/10^30,(134728804258574924699 : Int)/10^30)
theorem v2343_mg_checked : Scalar.distance (sourceCoefficient 28 34 3 2) v2343_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2343_upper : Scalar.QComplex := ((999997331241293533093317416699 : Int)/10^30,(-2310305237552124847420058670 : Int)/10^30)
theorem v2343_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 34 5) 1) 14) v2343_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2343 : Material (28 : Basis) (34 : Basis) where
  plus := ![v2343_pa,v2343_pb,v2343_pg]
  minus := ![(Primitive.Addresses.material2343 1).one,v2343_mb,v2343_mg]
  upper := v2343_upper
  lower := (Primitive.Addresses.material2343 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2343_pa_checked.trans (by decide +kernel)
    · exact v2343_pb_checked.trans (by decide +kernel)
    · exact v2343_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 34 Primitive.Addresses.material2343
    · exact v2343_mb_checked.trans (by decide +kernel)
    · exact v2343_mg_checked.trans (by decide +kernel)
  upper_error := v2343_upper_checked
  lower_error := reuse_lower_error 28 34 Primitive.Addresses.material2343

def v2344_pa : Scalar.QComplex := ((999999797905088907597714285008 : Int)/10^30,(-635759216482507221532111188 : Int)/10^30)
theorem v2344_pa_checked : Scalar.distance (sourceCoefficient 28 35 1 0) v2344_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2344_pb : Scalar.QComplex := ((-274315810137619651722002 : Int)/10^30,(-431477432946248337821579509 : Int)/10^30)
theorem v2344_pb_checked : Scalar.distance (sourceCoefficient 28 35 1 1) v2344_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2344_pg : Scalar.QComplex := ((-93086410992454698037010 : Int)/10^30,(59180555677820784378 : Int)/10^30)
theorem v2344_pg_checked : Scalar.distance (sourceCoefficient 28 35 1 2) v2344_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2344_mb : Scalar.QComplex := ((-646661299607726795043631 : Int)/10^30,(-431477035565291135778840151 : Int)/10^30)
theorem v2344_mb_checked : Scalar.distance (sourceCoefficient 28 35 3 1) v2344_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2344_mg : Scalar.QComplex := ((-93086325261975469723447 : Int)/10^30,(139509913872363818867 : Int)/10^30)
theorem v2344_mg_checked : Scalar.distance (sourceCoefficient 28 35 3 2) v2344_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2344_upper : Scalar.QComplex := ((999997211260126132697238804492 : Int)/10^30,(-2361667201505013369941843990 : Int)/10^30)
theorem v2344_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 35 5) 1) 14) v2344_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2344 : Material (28 : Basis) (35 : Basis) where
  plus := ![v2344_pa,v2344_pb,v2344_pg]
  minus := ![(Primitive.Addresses.material2344 1).one,v2344_mb,v2344_mg]
  upper := v2344_upper
  lower := (Primitive.Addresses.material2344 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2344_pa_checked.trans (by decide +kernel)
    · exact v2344_pb_checked.trans (by decide +kernel)
    · exact v2344_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 35 Primitive.Addresses.material2344
    · exact v2344_mb_checked.trans (by decide +kernel)
    · exact v2344_mg_checked.trans (by decide +kernel)
  upper_error := v2344_upper_checked
  lower_error := reuse_lower_error 28 35 Primitive.Addresses.material2344

def v2345_pa : Scalar.QComplex := ((999999787510475202258090248620 : Int)/10^30,(-651904137464769946318483653 : Int)/10^30)
theorem v2345_pa_checked : Scalar.distance (sourceCoefficient 28 36 1 0) v2345_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2345_pb : Scalar.QComplex := ((-281281980428717003237784 : Int)/10^30,(-431477428189269040694558712 : Int)/10^30)
theorem v2345_pb_checked : Scalar.distance (sourceCoefficient 28 36 1 1) v2345_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2345_pg : Scalar.QComplex := ((-93086409995523525775689 : Int)/10^30,(60683428712416633910 : Int)/10^30)
theorem v2345_pg_checked : Scalar.distance (sourceCoefficient 28 36 1 2) v2345_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2345_mb : Scalar.QComplex := ((-653627463199941690447507 : Int)/10^30,(-431477024796822393338763678 : Int)/10^30)
theorem v2345_mb_checked : Scalar.distance (sourceCoefficient 28 36 3 1) v2345_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2345_mg : Scalar.QComplex := ((-93086322968132926697769 : Int)/10^30,(141012785487064651380 : Int)/10^30)
theorem v2345_mg_checked : Scalar.distance (sourceCoefficient 28 36 3 2) v2345_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2345_upper : Scalar.QComplex := ((999997173000858949318476510280 : Int)/10^30,(-2377812080501152543862330258 : Int)/10^30)
theorem v2345_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 36 5) 1) 14) v2345_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2345 : Material (28 : Basis) (36 : Basis) where
  plus := ![v2345_pa,v2345_pb,v2345_pg]
  minus := ![(Primitive.Addresses.material2345 1).one,v2345_mb,v2345_mg]
  upper := v2345_upper
  lower := (Primitive.Addresses.material2345 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2345_pa_checked.trans (by decide +kernel)
    · exact v2345_pb_checked.trans (by decide +kernel)
    · exact v2345_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 36 Primitive.Addresses.material2345
    · exact v2345_mb_checked.trans (by decide +kernel)
    · exact v2345_mg_checked.trans (by decide +kernel)
  upper_error := v2345_upper_checked
  lower_error := reuse_lower_error 28 36 Primitive.Addresses.material2345

def v2346_pa : Scalar.QComplex := ((999999782992447026921251528406 : Int)/10^30,(-658798192813155377419726913 : Int)/10^30)
theorem v2346_pa_checked : Scalar.distance (sourceCoefficient 28 37 1 0) v2346_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2346_pb : Scalar.QComplex := ((-284256610248285949164849 : Int)/10^30,(-431477426112299278264712400 : Int)/10^30)
theorem v2346_pb_checked : Scalar.distance (sourceCoefficient 28 37 1 1) v2346_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2346_pg : Scalar.QComplex := ((-93086409561198517888890 : Int)/10^30,(61325171702408258231 : Int)/10^30)
theorem v2346_pg_checked : Scalar.distance (sourceCoefficient 28 37 1 2) v2346_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2346_mb : Scalar.QComplex := ((-656602090119588645519020 : Int)/10^30,(-431477020152881842325467632 : Int)/10^30)
theorem v2346_mb_checked : Scalar.distance (sourceCoefficient 28 37 3 1) v2346_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2346_mg : Scalar.QComplex := ((-93086321980012783198586 : Int)/10^30,(141654527863303110890 : Int)/10^30)
theorem v2346_mg_checked : Scalar.distance (sourceCoefficient 28 37 3 2) v2346_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2346_upper : Scalar.QComplex := ((999997156584323395556288791755 : Int)/10^30,(-2384706117783945607855270800 : Int)/10^30)
theorem v2346_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 37 5) 1) 14) v2346_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2346 : Material (28 : Basis) (37 : Basis) where
  plus := ![v2346_pa,v2346_pb,v2346_pg]
  minus := ![(Primitive.Addresses.material2346 1).one,v2346_mb,v2346_mg]
  upper := v2346_upper
  lower := (Primitive.Addresses.material2346 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2346_pa_checked.trans (by decide +kernel)
    · exact v2346_pb_checked.trans (by decide +kernel)
    · exact v2346_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 37 Primitive.Addresses.material2346
    · exact v2346_mb_checked.trans (by decide +kernel)
    · exact v2346_mg_checked.trans (by decide +kernel)
  upper_error := v2346_upper_checked
  lower_error := reuse_lower_error 28 37 Primitive.Addresses.material2346

def v2347_pa : Scalar.QComplex := ((999999767370311175495192130463 : Int)/10^30,(-682099203585840212314343247 : Int)/10^30)
theorem v2347_pa_checked : Scalar.distance (sourceCoefficient 28 38 1 0) v2347_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2347_pb : Scalar.QComplex := ((-294310472255514765680654 : Int)/10^30,(-431477418890026711255108577 : Int)/10^30)
theorem v2347_pb_checked : Scalar.distance (sourceCoefficient 28 38 1 1) v2347_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2347_pg : Scalar.QComplex := ((-93086408055031989387993 : Int)/10^30,(63494179569635096611 : Int)/10^30)
theorem v2347_pg_checked : Scalar.distance (sourceCoefficient 28 38 1 2) v2347_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2347_mb : Scalar.QComplex := ((-666655942150809206303030 : Int)/10^30,(-431477004254581861395286366 : Int)/10^30)
theorem v2347_mb_checked : Scalar.distance (sourceCoefficient 28 38 3 1) v2347_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2347_mg : Scalar.QComplex := ((-93086318602090714583534 : Int)/10^30,(143823533623155312870 : Int)/10^30)
theorem v2347_mg_checked : Scalar.distance (sourceCoefficient 28 38 3 2) v2347_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2347_upper : Scalar.QComplex := ((999997100746780068997248770586 : Int)/10^30,(-2408007066890122775366287115 : Int)/10^30)
theorem v2347_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 38 5) 1) 14) v2347_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2347 : Material (28 : Basis) (38 : Basis) where
  plus := ![v2347_pa,v2347_pb,v2347_pg]
  minus := ![(Primitive.Addresses.material2347 1).one,v2347_mb,v2347_mg]
  upper := v2347_upper
  lower := (Primitive.Addresses.material2347 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2347_pa_checked.trans (by decide +kernel)
    · exact v2347_pb_checked.trans (by decide +kernel)
    · exact v2347_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 38 Primitive.Addresses.material2347
    · exact v2347_mb_checked.trans (by decide +kernel)
    · exact v2347_mg_checked.trans (by decide +kernel)
  upper_error := v2347_upper_checked
  lower_error := reuse_lower_error 28 38 Primitive.Addresses.material2347

def v2348_pa : Scalar.QComplex := ((999999758058747758796013500501 : Int)/10^30,(-695616594070928153384501879 : Int)/10^30)
theorem v2348_pa_checked : Scalar.distance (sourceCoefficient 28 39 1 0) v2348_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2348_pb : Scalar.QComplex := ((-300142922149679201699584 : Int)/10^30,(-431477414557078362668191675 : Int)/10^30)
theorem v2348_pb_checked : Scalar.distance (sourceCoefficient 28 39 1 1) v2348_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2348_pg : Scalar.QComplex := ((-93086407154249417292767 : Int)/10^30,(64752465165231167029 : Int)/10^30)
theorem v2348_pg_checked : Scalar.distance (sourceCoefficient 28 39 1 2) v2348_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2348_mb : Scalar.QComplex := ((-672488386134146714515085 : Int)/10^30,(-431476994888493551291109326 : Int)/10^30)
theorem v2348_mb_checked : Scalar.distance (sourceCoefficient 28 39 3 1) v2348_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2348_mg : Scalar.QComplex := ((-93086316615464679970915 : Int)/10^30,(145081817972899359578 : Int)/10^30)
theorem v2348_mg_checked : Scalar.distance (sourceCoefficient 28 39 3 2) v2348_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2348_upper : Scalar.QComplex := ((999997068105440831601750298499 : Int)/10^30,(-2421524421171731734337360433 : Int)/10^30)
theorem v2348_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 39 5) 1) 14) v2348_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2348 : Material (28 : Basis) (39 : Basis) where
  plus := ![v2348_pa,v2348_pb,v2348_pg]
  minus := ![(Primitive.Addresses.material2348 1).one,v2348_mb,v2348_mg]
  upper := v2348_upper
  lower := (Primitive.Addresses.material2348 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2348_pa_checked.trans (by decide +kernel)
    · exact v2348_pb_checked.trans (by decide +kernel)
    · exact v2348_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 39 Primitive.Addresses.material2348
    · exact v2348_mb_checked.trans (by decide +kernel)
    · exact v2348_mg_checked.trans (by decide +kernel)
  upper_error := v2348_upper_checked
  lower_error := reuse_lower_error 28 39 Primitive.Addresses.material2348

def v2349_pa : Scalar.QComplex := ((999999741985106239113473522042 : Int)/10^30,(-718352087036773110616022616 : Int)/10^30)
theorem v2349_pa_checked : Scalar.distance (sourceCoefficient 28 40 1 0) v2349_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2349_pb : Scalar.QComplex := ((-309952775823237035353735 : Int)/10^30,(-431477407032211690382745519 : Int)/10^30)
theorem v2349_pb_checked : Scalar.distance (sourceCoefficient 28 40 1 1) v2349_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2349_pg : Scalar.QComplex := ((-93086405594427723376181 : Int)/10^30,(66868830986663030286 : Int)/10^30)
theorem v2349_pg_checked : Scalar.distance (sourceCoefficient 28 40 1 2) v2349_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2349_mb : Scalar.QComplex := ((-682298229661426662274445 : Int)/10^30,(-431476978898167779985367881 : Int)/10^30)
theorem v2349_mb_checked : Scalar.distance (sourceCoefficient 28 40 3 1) v2349_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2349_mg : Scalar.QComplex := ((-93086313229315180529777 : Int)/10^30,(147198181660255634731 : Int)/10^30)
theorem v2349_mg_checked : Scalar.distance (sourceCoefficient 28 40 3 2) v2349_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2349_upper : Scalar.QComplex := ((999997012792424940481837286073 : Int)/10^30,(-2444259852534083543948781914 : Int)/10^30)
theorem v2349_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 40 5) 1) 14) v2349_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2349 : Material (28 : Basis) (40 : Basis) where
  plus := ![v2349_pa,v2349_pb,v2349_pg]
  minus := ![(Primitive.Addresses.material2349 1).one,v2349_mb,v2349_mg]
  upper := v2349_upper
  lower := (Primitive.Addresses.material2349 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2349_pa_checked.trans (by decide +kernel)
    · exact v2349_pb_checked.trans (by decide +kernel)
    · exact v2349_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 40 Primitive.Addresses.material2349
    · exact v2349_mb_checked.trans (by decide +kernel)
    · exact v2349_mg_checked.trans (by decide +kernel)
  upper_error := v2349_upper_checked
  lower_error := reuse_lower_error 28 40 Primitive.Addresses.material2349

def v2350_pa : Scalar.QComplex := ((999999731475605644744216870623 : Int)/10^30,(-732836077581583862896798385 : Int)/10^30)
theorem v2350_pa_checked : Scalar.distance (sourceCoefficient 28 41 1 0) v2350_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2350_pb : Scalar.QComplex := ((-316202291815855190774779 : Int)/10^30,(-431477402083311999556654045 : Int)/10^30)
theorem v2350_pb_checked : Scalar.distance (sourceCoefficient 28 41 1 1) v2350_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2350_pg : Scalar.QComplex := ((-93086404571447011152168 : Int)/10^30,(68217093920265474235 : Int)/10^30)
theorem v2350_pg_checked : Scalar.distance (sourceCoefficient 28 41 1 2) v2350_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2350_mb : Scalar.QComplex := ((-688547739056386853638208 : Int)/10^30,(-431476968556219097983072501 : Int)/10^30)
theorem v2350_mb_checked : Scalar.distance (sourceCoefficient 28 41 3 1) v2350_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2350_mg : Scalar.QComplex := ((-93086311042844661017693 : Int)/10^30,(148546443209051888531 : Int)/10^30)
theorem v2350_mg_checked : Scalar.distance (sourceCoefficient 28 41 3 2) v2350_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2350_upper : Scalar.QComplex := ((999996977284886295793822245121 : Int)/10^30,(-2458743803368247177345721775 : Int)/10^30)
theorem v2350_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 41 5) 1) 14) v2350_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2350 : Material (28 : Basis) (41 : Basis) where
  plus := ![v2350_pa,v2350_pb,v2350_pg]
  minus := ![(Primitive.Addresses.material2350 1).one,v2350_mb,v2350_mg]
  upper := v2350_upper
  lower := (Primitive.Addresses.material2350 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2350_pa_checked.trans (by decide +kernel)
    · exact v2350_pb_checked.trans (by decide +kernel)
    · exact v2350_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 41 Primitive.Addresses.material2350
    · exact v2350_mb_checked.trans (by decide +kernel)
    · exact v2350_mg_checked.trans (by decide +kernel)
  upper_error := v2350_upper_checked
  lower_error := reuse_lower_error 28 41 Primitive.Addresses.material2350

def v2351_pa : Scalar.QComplex := ((999999722845151627868651202956 : Int)/10^30,(-744519724338752976610338841 : Int)/10^30)
theorem v2351_pa_checked : Scalar.distance (sourceCoefficient 28 42 1 0) v2351_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2351_pb : Scalar.QComplex := ((-321243522454012285372578 : Int)/10^30,(-431477398003290878815900620 : Int)/10^30)
theorem v2351_pb_checked : Scalar.distance (sourceCoefficient 28 42 1 1) v2351_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2351_pg : Scalar.QComplex := ((-93086403729648564855762 : Int)/10^30,(69304682852612683963 : Int)/10^30)
theorem v2351_pg_checked : Scalar.distance (sourceCoefficient 28 42 1 2) v2351_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2351_mb : Scalar.QComplex := ((-693588964296588916158797 : Int)/10^30,(-431476960125844504290578266 : Int)/10^30)
theorem v2351_mb_checked : Scalar.distance (sourceCoefficient 28 42 3 1) v2351_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2351_mg : Scalar.QComplex := ((-93086309262506262732851 : Int)/10^30,(149634031010005887518 : Int)/10^30)
theorem v2351_mg_checked : Scalar.distance (sourceCoefficient 28 42 3 2) v2351_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2351_upper : Scalar.QComplex := ((999996948489530762245894872279 : Int)/10^30,(-2470427417828616219358974769 : Int)/10^30)
theorem v2351_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 42 5) 1) 14) v2351_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2351 : Material (28 : Basis) (42 : Basis) where
  plus := ![v2351_pa,v2351_pb,v2351_pg]
  minus := ![(Primitive.Addresses.material2351 1).one,v2351_mb,v2351_mg]
  upper := v2351_upper
  lower := (Primitive.Addresses.material2351 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2351_pa_checked.trans (by decide +kernel)
    · exact v2351_pb_checked.trans (by decide +kernel)
    · exact v2351_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 42 Primitive.Addresses.material2351
    · exact v2351_mb_checked.trans (by decide +kernel)
    · exact v2351_mg_checked.trans (by decide +kernel)
  upper_error := v2351_upper_checked
  lower_error := reuse_lower_error 28 42 Primitive.Addresses.material2351

def v2352_pa : Scalar.QComplex := ((999999711201851868227657045648 : Int)/10^30,(-759997508455899032605603304 : Int)/10^30)
theorem v2352_pa_checked : Scalar.distance (sourceCoefficient 28 43 1 0) v2352_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2352_pb : Scalar.QComplex := ((-327921837941090638520692 : Int)/10^30,(-431477392477398732924423998 : Int)/10^30)
theorem v2352_pb_checked : Scalar.distance (sourceCoefficient 28 43 1 1) v2352_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2352_pg : Scalar.QComplex := ((-93086402591657372995527 : Int)/10^30,(70745454471938586193 : Int)/10^30)
theorem v2352_pg_checked : Scalar.distance (sourceCoefficient 28 43 1 2) v2352_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2352_mb : Scalar.QComplex := ((-700267272528429154411160 : Int)/10^30,(-431476948836868930756728021 : Int)/10^30)
theorem v2352_mb_checked : Scalar.distance (sourceCoefficient 28 43 3 1) v2352_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2352_mg : Scalar.QComplex := ((-93086306881194477065398 : Int)/10^30,(151074801110831524002 : Int)/10^30)
theorem v2352_mg_checked : Scalar.distance (sourceCoefficient 28 43 3 2) v2352_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2352_upper : Scalar.QComplex := ((999996910132997091344699674061 : Int)/10^30,(-2485905158798141867868232178 : Int)/10^30)
theorem v2352_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 43 5) 1) 14) v2352_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2352 : Material (28 : Basis) (43 : Basis) where
  plus := ![v2352_pa,v2352_pb,v2352_pg]
  minus := ![(Primitive.Addresses.material2352 1).one,v2352_mb,v2352_mg]
  upper := v2352_upper
  lower := (Primitive.Addresses.material2352 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2352_pa_checked.trans (by decide +kernel)
    · exact v2352_pb_checked.trans (by decide +kernel)
    · exact v2352_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 43 Primitive.Addresses.material2352
    · exact v2352_mb_checked.trans (by decide +kernel)
    · exact v2352_mg_checked.trans (by decide +kernel)
  upper_error := v2352_upper_checked
  lower_error := reuse_lower_error 28 43 Primitive.Addresses.material2352

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
