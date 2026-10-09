import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B104
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B105

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2513_pa : Scalar.QComplex := ((999999274443753343800536047277 : Int)/10^30,(-1204621088508968394306675362 : Int)/10^30)
theorem v2513_pa_checked : Scalar.distance (sourceCoefficient 30 69 1 0) v2513_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2513_pb : Scalar.QComplex := ((-519766885539208781244820 : Int)/10^30,(-431477178489747579878128372 : Int)/10^30)
theorem v2513_pb_checked : Scalar.distance (sourceCoefficient 30 69 1 1) v2513_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2513_pg : Scalar.QComplex := ((-93086359180814931811383 : Int)/10^30,(112133872681161872217 : Int)/10^30)
theorem v2513_pg_checked : Scalar.distance (sourceCoefficient 30 69 1 2) v2513_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2513_mb : Scalar.QComplex := ((-892112064032163025507684 : Int)/10^30,(-431476569295661758114547790 : Int)/10^30)
theorem v2513_mb_checked : Scalar.distance (sourceCoefficient 30 69 3 1) v2513_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2513_mg : Scalar.QComplex := ((-93086227754027350320965 : Int)/10^30,(192463166447653291599 : Int)/10^30)
theorem v2513_mg_checked : Scalar.distance (sourceCoefficient 30 69 3 2) v2513_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2513_upper : Scalar.QComplex := ((999995705995585831297775412061 : Int)/10^30,(-2930527322831762227157365488 : Int)/10^30)
theorem v2513_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 69 5) 1) 14) v2513_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2513 : Material (30 : Basis) (69 : Basis) where
  plus := ![v2513_pa,v2513_pb,v2513_pg]
  minus := ![(Primitive.Addresses.material2513 1).one,v2513_mb,v2513_mg]
  upper := v2513_upper
  lower := (Primitive.Addresses.material2513 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2513_pa_checked.trans (by decide +kernel)
    · exact v2513_pb_checked.trans (by decide +kernel)
    · exact v2513_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 69 Primitive.Addresses.material2513
    · exact v2513_mb_checked.trans (by decide +kernel)
    · exact v2513_mg_checked.trans (by decide +kernel)
  upper_error := v2513_upper_checked
  lower_error := reuse_lower_error 30 69 Primitive.Addresses.material2513

def v2514_pa : Scalar.QComplex := ((999999257198352414706346450048 : Int)/10^30,(-1218853044224897381321442100 : Int)/10^30)
theorem v2514_pa_checked : Scalar.distance (sourceCoefficient 30 70 1 0) v2514_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2514_pb : Scalar.QComplex := ((-525907652477049769952538 : Int)/10^30,(-431477169724278053913569717 : Int)/10^30)
theorem v2514_pb_checked : Scalar.distance (sourceCoefficient 30 70 1 1) v2514_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2514_pg : Scalar.QComplex := ((-93086357432632719456203 : Int)/10^30,(113458674409861577555 : Int)/10^30)
theorem v2514_pg_checked : Scalar.distance (sourceCoefficient 30 70 1 2) v2514_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2514_mb : Scalar.QComplex := ((-898252821119310417528939 : Int)/10^30,(-431476555230990198454246107 : Int)/10^30)
theorem v2514_mb_checked : Scalar.distance (sourceCoefficient 30 70 3 1) v2514_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2514_mg : Scalar.QComplex := ((-93086224862601563880996 : Int)/10^30,(193787966174466252853 : Int)/10^30)
theorem v2514_mg_checked : Scalar.distance (sourceCoefficient 30 70 3 2) v2514_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2514_upper : Scalar.QComplex := ((999995664187146134445979313286 : Int)/10^30,(-2944759227586867465186638196 : Int)/10^30)
theorem v2514_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 70 5) 1) 14) v2514_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2514 : Material (30 : Basis) (70 : Basis) where
  plus := ![v2514_pa,v2514_pb,v2514_pg]
  minus := ![(Primitive.Addresses.material2514 1).one,v2514_mb,v2514_mg]
  upper := v2514_upper
  lower := (Primitive.Addresses.material2514 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2514_pa_checked.trans (by decide +kernel)
    · exact v2514_pb_checked.trans (by decide +kernel)
    · exact v2514_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 70 Primitive.Addresses.material2514
    · exact v2514_mb_checked.trans (by decide +kernel)
    · exact v2514_mg_checked.trans (by decide +kernel)
  upper_error := v2514_upper_checked
  lower_error := reuse_lower_error 30 70 Primitive.Addresses.material2514

def v2515_pa : Scalar.QComplex := ((999999227293908817061537707963 : Int)/10^30,(-1243145842325498659095589708 : Int)/10^30)
theorem v2515_pa_checked : Scalar.distance (sourceCoefficient 30 71 1 0) v2515_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2515_pb : Scalar.QComplex := ((-536389445137955300202000 : Int)/10^30,(-431477154493123873272345760 : Int)/10^30)
theorem v2515_pb_checked : Scalar.distance (sourceCoefficient 30 71 1 1) v2515_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2515_pg : Scalar.QComplex := ((-93086354397808533366226 : Int)/10^30,(115720003864425433458 : Int)/10^30)
theorem v2515_pg_checked : Scalar.distance (sourceCoefficient 30 71 1 2) v2515_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2515_mb : Scalar.QComplex := ((-908734596733565426359466 : Int)/10^30,(-431476530954526705123273254 : Int)/10^30)
theorem v2515_mb_checked : Scalar.distance (sourceCoefficient 30 71 3 1) v2515_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2515_mg : Scalar.QComplex := ((-93086219876353035004067 : Int)/10^30,(196049292168117215772 : Int)/10^30)
theorem v2515_mg_checked : Scalar.distance (sourceCoefficient 30 71 3 2) v2515_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2515_upper : Scalar.QComplex := ((999995592355581379747628169458 : Int)/10^30,(-2969051937893842865032979677 : Int)/10^30)
theorem v2515_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 71 5) 1) 14) v2515_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2515 : Material (30 : Basis) (71 : Basis) where
  plus := ![v2515_pa,v2515_pb,v2515_pg]
  minus := ![(Primitive.Addresses.material2515 1).one,v2515_mb,v2515_mg]
  upper := v2515_upper
  lower := (Primitive.Addresses.material2515 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2515_pa_checked.trans (by decide +kernel)
    · exact v2515_pb_checked.trans (by decide +kernel)
    · exact v2515_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 71 Primitive.Addresses.material2515
    · exact v2515_mb_checked.trans (by decide +kernel)
    · exact v2515_mg_checked.trans (by decide +kernel)
  upper_error := v2515_upper_checked
  lower_error := reuse_lower_error 30 71 Primitive.Addresses.material2515

def v2516_pa : Scalar.QComplex := ((999999194173825941091441086081 : Int)/10^30,(-1269508447692253176449415695 : Int)/10^30)
theorem v2516_pa_checked : Scalar.distance (sourceCoefficient 30 72 1 0) v2516_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2516_pb : Scalar.QComplex := ((-547764312546834968437629 : Int)/10^30,(-431477137580104091862159446 : Int)/10^30)
theorem v2516_pb_checked : Scalar.distance (sourceCoefficient 30 72 1 1) v2516_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2516_pg : Scalar.QComplex := ((-93086351031896348186309 : Int)/10^30,(118174004227544602540 : Int)/10^30)
theorem v2516_pg_checked : Scalar.distance (sourceCoefficient 30 72 1 2) v2516_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2516_mb : Scalar.QComplex := ((-920109445311887763924209 : Int)/10^30,(-431476504225514952350601080 : Int)/10^30)
theorem v2516_mb_checked : Scalar.distance (sourceCoefficient 30 72 3 1) v2516_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2516_mg : Scalar.QComplex := ((-93086214392750313808752 : Int)/10^30,(198503288712869275556 : Int)/10^30)
theorem v2516_mg_checked : Scalar.distance (sourceCoefficient 30 72 3 2) v2516_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2516_upper : Scalar.QComplex := ((999995513736082566108862534828 : Int)/10^30,(-2995414446834335044291736200 : Int)/10^30)
theorem v2516_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 72 5) 1) 14) v2516_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2516 : Material (30 : Basis) (72 : Basis) where
  plus := ![v2516_pa,v2516_pb,v2516_pg]
  minus := ![(Primitive.Addresses.material2516 1).one,v2516_mb,v2516_mg]
  upper := v2516_upper
  lower := (Primitive.Addresses.material2516 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2516_pa_checked.trans (by decide +kernel)
    · exact v2516_pb_checked.trans (by decide +kernel)
    · exact v2516_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 72 Primitive.Addresses.material2516
    · exact v2516_mb_checked.trans (by decide +kernel)
    · exact v2516_mg_checked.trans (by decide +kernel)
  upper_error := v2516_upper_checked
  lower_error := reuse_lower_error 30 72 Primitive.Addresses.material2516

def v2517_pa : Scalar.QComplex := ((999999182132776957582179152164 : Int)/10^30,(-1278958082650890132205284550 : Int)/10^30)
theorem v2517_pa_checked : Scalar.distance (sourceCoefficient 30 73 1 0) v2517_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2517_pb : Scalar.QComplex := ((-551841616042200108946391 : Int)/10^30,(-431477131420313296990678074 : Int)/10^30)
theorem v2517_pb_checked : Scalar.distance (sourceCoefficient 30 73 1 1) v2517_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2517_pg : Scalar.QComplex := ((-93086349807014369924862 : Int)/10^30,(119053636840216510846 : Int)/10^30)
theorem v2517_pg_checked : Scalar.distance (sourceCoefficient 30 73 1 2) v2517_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2517_mb : Scalar.QComplex := ((-924186741973464441838062 : Int)/10^30,(-431476494547197169483214846 : Int)/10^30)
theorem v2517_mb_checked : Scalar.distance (sourceCoefficient 30 73 3 1) v2517_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2517_mg : Scalar.QComplex := ((-93086212408785464073205 : Int)/10^30,(199382919940995780364 : Int)/10^30)
theorem v2517_mg_checked : Scalar.distance (sourceCoefficient 30 73 3 2) v2517_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2517_upper : Scalar.QComplex := ((999995485385838841907102145039 : Int)/10^30,(-3004864046937092571149388434 : Int)/10^30)
theorem v2517_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 73 5) 1) 14) v2517_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2517 : Material (30 : Basis) (73 : Basis) where
  plus := ![v2517_pa,v2517_pb,v2517_pg]
  minus := ![(Primitive.Addresses.material2517 1).one,v2517_mb,v2517_mg]
  upper := v2517_upper
  lower := (Primitive.Addresses.material2517 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2517_pa_checked.trans (by decide +kernel)
    · exact v2517_pb_checked.trans (by decide +kernel)
    · exact v2517_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 73 Primitive.Addresses.material2517
    · exact v2517_mb_checked.trans (by decide +kernel)
    · exact v2517_mg_checked.trans (by decide +kernel)
  upper_error := v2517_upper_checked
  lower_error := reuse_lower_error 30 73 Primitive.Addresses.material2517

def v2518_pa : Scalar.QComplex := ((999999168476865182117885652913 : Int)/10^30,(-1289591244621736911758165624 : Int)/10^30)
theorem v2518_pa_checked : Scalar.distance (sourceCoefficient 30 74 1 0) v2518_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2518_pb : Scalar.QComplex := ((-556429584600479969980578 : Int)/10^30,(-431477124427608336600659540 : Int)/10^30)
theorem v2518_pb_checked : Scalar.distance (sourceCoefficient 30 74 1 1) v2518_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2518_pg : Scalar.QComplex := ((-93086348417125546440786 : Int)/10^30,(120043439731430902931 : Int)/10^30)
theorem v2518_pg_checked : Scalar.distance (sourceCoefficient 30 74 1 2) v2518_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2518_mb : Scalar.QComplex := ((-928774702789044487026832 : Int)/10^30,(-431476483595284581434549599 : Int)/10^30)
theorem v2518_mb_checked : Scalar.distance (sourceCoefficient 30 74 3 1) v2518_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2518_mg : Scalar.QComplex := ((-93086210164741842057606 : Int)/10^30,(200372721264249863425 : Int)/10^30)
theorem v2518_mg_checked : Scalar.distance (sourceCoefficient 30 74 3 2) v2518_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2518_upper : Scalar.QComplex := ((999995453378074476556416994083 : Int)/10^30,(-3015497169502228784260190658 : Int)/10^30)
theorem v2518_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 74 5) 1) 14) v2518_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2518 : Material (30 : Basis) (74 : Basis) where
  plus := ![v2518_pa,v2518_pb,v2518_pg]
  minus := ![(Primitive.Addresses.material2518 1).one,v2518_mb,v2518_mg]
  upper := v2518_upper
  lower := (Primitive.Addresses.material2518 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2518_pa_checked.trans (by decide +kernel)
    · exact v2518_pb_checked.trans (by decide +kernel)
    · exact v2518_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 74 Primitive.Addresses.material2518
    · exact v2518_mb_checked.trans (by decide +kernel)
    · exact v2518_mg_checked.trans (by decide +kernel)
  upper_error := v2518_upper_checked
  lower_error := reuse_lower_error 30 74 Primitive.Addresses.material2518

def v2519_pa : Scalar.QComplex := ((999999149261660680684092517676 : Int)/10^30,(-1304406361101826974365233050 : Int)/10^30)
theorem v2519_pa_checked : Scalar.distance (sourceCoefficient 30 75 1 0) v2519_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2519_pb : Scalar.QComplex := ((-562821971737373937880994 : Int)/10^30,(-431477114576266897336446603 : Int)/10^30)
theorem v2519_pb_checked : Scalar.distance (sourceCoefficient 30 75 1 1) v2519_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2519_pg : Scalar.QComplex := ((-93086346460130006463292 : Int)/10^30,(121422525753120029499 : Int)/10^30)
theorem v2519_pg_checked : Scalar.distance (sourceCoefficient 30 75 1 2) v2519_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2519_mb : Scalar.QComplex := ((-935167079044496603200075 : Int)/10^30,(-431476468227604613564693912 : Int)/10^30)
theorem v2519_mb_checked : Scalar.distance (sourceCoefficient 30 75 3 1) v2519_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2519_mg : Scalar.QComplex := ((-93086207017657905769995 : Int)/10^30,(201751805083643225580 : Int)/10^30)
theorem v2519_mg_checked : Scalar.distance (sourceCoefficient 30 75 3 2) v2519_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2519_upper : Scalar.QComplex := ((999995408593351566145294363965 : Int)/10^30,(-3030312230753243375865270382 : Int)/10^30)
theorem v2519_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 75 5) 1) 14) v2519_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2519 : Material (30 : Basis) (75 : Basis) where
  plus := ![v2519_pa,v2519_pb,v2519_pg]
  minus := ![(Primitive.Addresses.material2519 1).one,v2519_mb,v2519_mg]
  upper := v2519_upper
  lower := (Primitive.Addresses.material2519 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2519_pa_checked.trans (by decide +kernel)
    · exact v2519_pb_checked.trans (by decide +kernel)
    · exact v2519_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 75 Primitive.Addresses.material2519
    · exact v2519_mb_checked.trans (by decide +kernel)
    · exact v2519_mg_checked.trans (by decide +kernel)
  upper_error := v2519_upper_checked
  lower_error := reuse_lower_error 30 75 Primitive.Addresses.material2519

def v2520_pa : Scalar.QComplex := ((999999132970393655382292300811 : Int)/10^30,(-1316836535394160886544763002 : Int)/10^30)
theorem v2520_pa_checked : Scalar.distance (sourceCoefficient 30 76 1 0) v2520_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2520_pb : Scalar.QComplex := ((-568185310281411847241887 : Int)/10^30,(-431477106213380193348045280 : Int)/10^30)
theorem v2520_pb_checked : Scalar.distance (sourceCoefficient 30 76 1 1) v2520_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2520_pg : Scalar.QComplex := ((-93086344799782614344091 : Int)/10^30,(122579606058799589857 : Int)/10^30)
theorem v2520_pg_checked : Scalar.distance (sourceCoefficient 30 76 1 2) v2520_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2520_mb : Scalar.QComplex := ((-940530408374723880828418 : Int)/10^30,(-431476455236401415757550146 : Int)/10^30)
theorem v2520_mb_checked : Scalar.distance (sourceCoefficient 30 76 3 1) v2520_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2520_mg : Scalar.QComplex := ((-93086204358802941034993 : Int)/10^30,(202908883525683886823 : Int)/10^30)
theorem v2520_mg_checked : Scalar.distance (sourceCoefficient 30 76 3 2) v2520_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2520_upper : Scalar.QComplex := ((999995370848755632806719817673 : Int)/10^30,(-3042742358415043876984473472 : Int)/10^30)
theorem v2520_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 76 5) 1) 14) v2520_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2520 : Material (30 : Basis) (76 : Basis) where
  plus := ![v2520_pa,v2520_pb,v2520_pg]
  minus := ![(Primitive.Addresses.material2520 1).one,v2520_mb,v2520_mg]
  upper := v2520_upper
  lower := (Primitive.Addresses.material2520 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2520_pa_checked.trans (by decide +kernel)
    · exact v2520_pb_checked.trans (by decide +kernel)
    · exact v2520_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 76 Primitive.Addresses.material2520
    · exact v2520_mb_checked.trans (by decide +kernel)
    · exact v2520_mg_checked.trans (by decide +kernel)
  upper_error := v2520_upper_checked
  lower_error := reuse_lower_error 30 76 Primitive.Addresses.material2520

def v2521_pa : Scalar.QComplex := ((999999129176801250346055528828 : Int)/10^30,(-1319714226325633123946112210 : Int)/10^30)
theorem v2521_pa_checked : Scalar.distance (sourceCoefficient 30 77 1 0) v2521_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2521_pb : Scalar.QComplex := ((-569426968702034306400220 : Int)/10^30,(-431477104264629431677209974 : Int)/10^30)
theorem v2521_pb_checked : Scalar.distance (sourceCoefficient 30 77 1 1) v2521_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2521_pg : Scalar.QComplex := ((-93086344413006080578488 : Int)/10^30,(122847479976927212934 : Int)/10^30)
theorem v2521_pg_checked : Scalar.distance (sourceCoefficient 30 77 1 2) v2521_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2521_mb : Scalar.QComplex := ((-941772064651336024550104 : Int)/10^30,(-431476452216156084917837940 : Int)/10^30)
theorem v2521_mb_checked : Scalar.distance (sourceCoefficient 30 77 3 1) v2521_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2521_mg : Scalar.QComplex := ((-93086203740863424533246 : Int)/10^30,(203176757010299078866 : Int)/10^30)
theorem v2521_mg_checked : Scalar.distance (sourceCoefficient 30 77 3 2) v2521_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2521_upper : Scalar.QComplex := ((999995362088535392241660015564 : Int)/10^30,(-3045620038513137170202634797 : Int)/10^30)
theorem v2521_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 77 5) 1) 14) v2521_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2521 : Material (30 : Basis) (77 : Basis) where
  plus := ![v2521_pa,v2521_pb,v2521_pg]
  minus := ![(Primitive.Addresses.material2521 1).one,v2521_mb,v2521_mg]
  upper := v2521_upper
  lower := (Primitive.Addresses.material2521 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2521_pa_checked.trans (by decide +kernel)
    · exact v2521_pb_checked.trans (by decide +kernel)
    · exact v2521_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 77 Primitive.Addresses.material2521
    · exact v2521_mb_checked.trans (by decide +kernel)
    · exact v2521_mg_checked.trans (by decide +kernel)
  upper_error := v2521_upper_checked
  lower_error := reuse_lower_error 30 77 Primitive.Addresses.material2521

def v2522_pa : Scalar.QComplex := ((999999106196649441007816664296 : Int)/10^30,(-1337013800315297753879325350 : Int)/10^30)
theorem v2522_pa_checked : Scalar.distance (sourceCoefficient 30 78 1 0) v2522_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2522_pb : Scalar.QComplex := ((-576891342751754668526855 : Int)/10^30,(-431477092449080069654468820 : Int)/10^30)
theorem v2522_pb_checked : Scalar.distance (sourceCoefficient 30 78 1 1) v2522_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2522_pg : Scalar.QComplex := ((-93086342068899886972821 : Int)/10^30,(124457835207819726340 : Int)/10^30)
theorem v2522_pg_checked : Scalar.distance (sourceCoefficient 30 78 1 2) v2522_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2522_mb : Scalar.QComplex := ((-949236425725441842382388 : Int)/10^30,(-431476433959192500382951557 : Int)/10^30)
theorem v2522_mb_checked : Scalar.distance (sourceCoefficient 30 78 3 1) v2522_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2522_mg : Scalar.QComplex := ((-93086200007094067192451 : Int)/10^30,(204787109618724672484 : Int)/10^30)
theorem v2522_mg_checked : Scalar.distance (sourceCoefficient 30 78 3 2) v2522_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2522_upper : Scalar.QComplex := ((999995309250922508071774211713 : Int)/10^30,(-3062919547075461213411232901 : Int)/10^30)
theorem v2522_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 78 5) 1) 14) v2522_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2522 : Material (30 : Basis) (78 : Basis) where
  plus := ![v2522_pa,v2522_pb,v2522_pg]
  minus := ![(Primitive.Addresses.material2522 1).one,v2522_mb,v2522_mg]
  upper := v2522_upper
  lower := (Primitive.Addresses.material2522 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2522_pa_checked.trans (by decide +kernel)
    · exact v2522_pb_checked.trans (by decide +kernel)
    · exact v2522_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 78 Primitive.Addresses.material2522
    · exact v2522_mb_checked.trans (by decide +kernel)
    · exact v2522_mg_checked.trans (by decide +kernel)
  upper_error := v2522_upper_checked
  lower_error := reuse_lower_error 30 78 Primitive.Addresses.material2522

def v2523_pa : Scalar.QComplex := ((999999098724463182370682049237 : Int)/10^30,(-1342590876379571324396349933 : Int)/10^30)
theorem v2523_pa_checked : Scalar.distance (sourceCoefficient 30 79 1 0) v2523_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2523_pb : Scalar.QComplex := ((-579297724632419567782257 : Int)/10^30,(-431477088603256300171136636 : Int)/10^30)
theorem v2523_pb_checked : Scalar.distance (sourceCoefficient 30 79 1 1) v2523_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2523_pg : Scalar.QComplex := ((-93086341306273669209262 : Int)/10^30,(124976985192057274513 : Int)/10^30)
theorem v2523_pg_checked : Scalar.distance (sourceCoefficient 30 79 1 2) v2523_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2523_mb : Scalar.QComplex := ((-951642803391328086789946 : Int)/10^30,(-431476428036770979278435609 : Int)/10^30)
theorem v2523_mb_checked : Scalar.distance (sourceCoefficient 30 79 3 1) v2523_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2523_mg : Scalar.QComplex := ((-93086198796465078639805 : Int)/10^30,(205306258751546876678 : Int)/10^30)
theorem v2523_mg_checked : Scalar.distance (sourceCoefficient 30 79 3 2) v2523_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2523_upper : Scalar.QComplex := ((999995292153220039830443450296 : Int)/10^30,(-3068496601937019504602060440 : Int)/10^30)
theorem v2523_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 79 5) 1) 14) v2523_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2523 : Material (30 : Basis) (79 : Basis) where
  plus := ![v2523_pa,v2523_pb,v2523_pg]
  minus := ![(Primitive.Addresses.material2523 1).one,v2523_mb,v2523_mg]
  upper := v2523_upper
  lower := (Primitive.Addresses.material2523 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2523_pa_checked.trans (by decide +kernel)
    · exact v2523_pb_checked.trans (by decide +kernel)
    · exact v2523_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 79 Primitive.Addresses.material2523
    · exact v2523_mb_checked.trans (by decide +kernel)
    · exact v2523_mg_checked.trans (by decide +kernel)
  upper_error := v2523_upper_checked
  lower_error := reuse_lower_error 30 79 Primitive.Addresses.material2523

def v2524_pa : Scalar.QComplex := ((999999086989927056130408354240 : Int)/10^30,(-1351302820355358351947777639 : Int)/10^30)
theorem v2524_pa_checked : Scalar.distance (sourceCoefficient 30 80 1 0) v2524_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2524_pb : Scalar.QComplex := ((-583056730918551039950909 : Int)/10^30,(-431477082559891075065440553 : Int)/10^30)
theorem v2524_pb_checked : Scalar.distance (sourceCoefficient 30 80 1 1) v2524_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2524_pg : Scalar.QComplex := ((-93086340108216538993538 : Int)/10^30,(125787948770455405096 : Int)/10^30)
theorem v2524_pg_checked : Scalar.distance (sourceCoefficient 30 80 1 2) v2524_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2524_mb : Scalar.QComplex := ((-955401803062657717357339 : Int)/10^30,(-431476418749554878820787549 : Int)/10^30)
theorem v2524_mb_checked : Scalar.distance (sourceCoefficient 30 80 3 1) v2524_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2524_mg : Scalar.QComplex := ((-93086196898583350801637 : Int)/10^30,(206117220994116859271 : Int)/10^30)
theorem v2524_mg_checked : Scalar.distance (sourceCoefficient 30 80 3 2) v2524_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2524_upper : Scalar.QComplex := ((999995265382676429978560111748 : Int)/10^30,(-3077208512684644551957269043 : Int)/10^30)
theorem v2524_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 80 5) 1) 14) v2524_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2524 : Material (30 : Basis) (80 : Basis) where
  plus := ![v2524_pa,v2524_pb,v2524_pg]
  minus := ![(Primitive.Addresses.material2524 1).one,v2524_mb,v2524_mg]
  upper := v2524_upper
  lower := (Primitive.Addresses.material2524 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2524_pa_checked.trans (by decide +kernel)
    · exact v2524_pb_checked.trans (by decide +kernel)
    · exact v2524_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 80 Primitive.Addresses.material2524
    · exact v2524_mb_checked.trans (by decide +kernel)
    · exact v2524_mg_checked.trans (by decide +kernel)
  upper_error := v2524_upper_checked
  lower_error := reuse_lower_error 30 80 Primitive.Addresses.material2524

def v2525_pa : Scalar.QComplex := ((999999051198300803369940086778 : Int)/10^30,(-1377534935371366805400133002 : Int)/10^30)
theorem v2525_pa_checked : Scalar.distance (sourceCoefficient 30 81 1 0) v2525_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2525_pb : Scalar.QComplex := ((-594375293552581625574864 : Int)/10^30,(-431477064099326732132297808 : Int)/10^30)
theorem v2525_pb_checked : Scalar.distance (sourceCoefficient 30 81 1 1) v2525_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2525_pg : Scalar.QComplex := ((-93086336451029453621045 : Int)/10^30,(128229802131680314657 : Int)/10^30)
theorem v2525_pg_checked : Scalar.distance (sourceCoefficient 30 81 1 2) v2525_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2525_mb : Scalar.QComplex := ((-966720345551634555467452 : Int)/10^30,(-431476390521587625568560599 : Int)/10^30)
theorem v2525_mb_checked : Scalar.distance (sourceCoefficient 30 81 3 1) v2525_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2525_mg : Scalar.QComplex := ((-93086191134188153422793 : Int)/10^30,(208559070290140423152 : Int)/10^30)
theorem v2525_mg_checked : Scalar.distance (sourceCoefficient 30 81 3 2) v2525_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2525_upper : Scalar.QComplex := ((999995184316852725895020961880 : Int)/10^30,(-3103440526857899208459196427 : Int)/10^30)
theorem v2525_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 81 5) 1) 14) v2525_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2525 : Material (30 : Basis) (81 : Basis) where
  plus := ![v2525_pa,v2525_pb,v2525_pg]
  minus := ![(Primitive.Addresses.material2525 1).one,v2525_mb,v2525_mg]
  upper := v2525_upper
  lower := (Primitive.Addresses.material2525 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2525_pa_checked.trans (by decide +kernel)
    · exact v2525_pb_checked.trans (by decide +kernel)
    · exact v2525_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 81 Primitive.Addresses.material2525
    · exact v2525_mb_checked.trans (by decide +kernel)
    · exact v2525_mg_checked.trans (by decide +kernel)
  upper_error := v2525_upper_checked
  lower_error := reuse_lower_error 30 81 Primitive.Addresses.material2525

def v2526_pa : Scalar.QComplex := ((999999037455842569842746389148 : Int)/10^30,(-1387475184775951048537187119 : Int)/10^30)
theorem v2526_pa_checked : Scalar.distance (sourceCoefficient 30 82 1 0) v2526_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2526_pb : Scalar.QComplex := ((-598664285629240265479012 : Int)/10^30,(-431477057000555907712451245 : Int)/10^30)
theorem v2526_pb_checked : Scalar.distance (sourceCoefficient 30 82 1 1) v2526_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2526_pg : Scalar.QComplex := ((-93086335045671219491369 : Int)/10^30,(129155104235099746729 : Int)/10^30)
theorem v2526_pg_checked : Scalar.distance (sourceCoefficient 30 82 1 2) v2526_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2526_mb : Scalar.QComplex := ((-971009329905385923905427 : Int)/10^30,(-431476379721612451221476742 : Int)/10^30)
theorem v2526_mb_checked : Scalar.distance (sourceCoefficient 30 82 3 1) v2526_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2526_mg : Scalar.QComplex := ((-93086188930336401380970 : Int)/10^30,(209484370836266732657 : Int)/10^30)
theorem v2526_mg_checked : Scalar.distance (sourceCoefficient 30 82 3 2) v2526_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2526_upper : Scalar.QComplex := ((999995153418446260214384519891 : Int)/10^30,(-3113380737739413422191261284 : Int)/10^30)
theorem v2526_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 82 5) 1) 14) v2526_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2526 : Material (30 : Basis) (82 : Basis) where
  plus := ![v2526_pa,v2526_pb,v2526_pg]
  minus := ![(Primitive.Addresses.material2526 1).one,v2526_mb,v2526_mg]
  upper := v2526_upper
  lower := (Primitive.Addresses.material2526 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2526_pa_checked.trans (by decide +kernel)
    · exact v2526_pb_checked.trans (by decide +kernel)
    · exact v2526_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 82 Primitive.Addresses.material2526
    · exact v2526_mb_checked.trans (by decide +kernel)
    · exact v2526_mg_checked.trans (by decide +kernel)
  upper_error := v2526_upper_checked
  lower_error := reuse_lower_error 30 82 Primitive.Addresses.material2526

def v2527_pa : Scalar.QComplex := ((999999018537664245920779420171 : Int)/10^30,(-1401043792406162419633260946 : Int)/10^30)
theorem v2527_pa_checked : Scalar.distance (sourceCoefficient 30 83 1 0) v2527_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2527_pb : Scalar.QComplex := ((-604518831884186810321400 : Int)/10^30,(-431477047218858309908737010 : Int)/10^30)
theorem v2527_pb_checked : Scalar.distance (sourceCoefficient 30 83 1 1) v2527_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2527_pg : Scalar.QComplex := ((-93086333110012670167047 : Int)/10^30,(130418157162144627971 : Int)/10^30)
theorem v2527_pg_checked : Scalar.distance (sourceCoefficient 30 83 1 2) v2527_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2527_mb : Scalar.QComplex := ((-976863865539252856450505 : Int)/10^30,(-431476364887708756547054773 : Int)/10^30)
theorem v2527_mb_checked : Scalar.distance (sourceCoefficient 30 83 3 1) v2527_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2527_mg : Scalar.QComplex := ((-93086185904720782543192 : Int)/10^30,(210747421622633135548 : Int)/10^30)
theorem v2527_mg_checked : Scalar.distance (sourceCoefficient 30 83 3 2) v2527_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2527_upper : Scalar.QComplex := ((999995111082110277420599579105 : Int)/10^30,(-3126949292509718065345420015 : Int)/10^30)
theorem v2527_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 83 5) 1) 14) v2527_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2527 : Material (30 : Basis) (83 : Basis) where
  plus := ![v2527_pa,v2527_pb,v2527_pg]
  minus := ![(Primitive.Addresses.material2527 1).one,v2527_mb,v2527_mg]
  upper := v2527_upper
  lower := (Primitive.Addresses.material2527 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2527_pa_checked.trans (by decide +kernel)
    · exact v2527_pb_checked.trans (by decide +kernel)
    · exact v2527_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 83 Primitive.Addresses.material2527
    · exact v2527_mb_checked.trans (by decide +kernel)
    · exact v2527_mg_checked.trans (by decide +kernel)
  upper_error := v2527_upper_checked
  lower_error := reuse_lower_error 30 83 Primitive.Addresses.material2527

def v2528_pa : Scalar.QComplex := ((999998968688930249927450875528 : Int)/10^30,(-1436182814232792060536293730 : Int)/10^30)
theorem v2528_pa_checked : Scalar.distance (sourceCoefficient 30 84 1 0) v2528_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2528_pb : Scalar.QComplex := ((-619680521946633581544136 : Int)/10^30,(-431477021394580735174874739 : Int)/10^30)
theorem v2528_pb_checked : Scalar.distance (sourceCoefficient 30 84 1 1) v2528_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2528_pg : Scalar.QComplex := ((-93086328004243374847014 : Int)/10^30,(133689122394802843065 : Int)/10^30)
theorem v2528_pg_checked : Scalar.distance (sourceCoefficient 30 84 1 2) v2528_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2528_mb : Scalar.QComplex := ((-992025527671121029248339 : Int)/10^30,(-431476325979585130651960661 : Int)/10^30)
theorem v2528_mb_checked : Scalar.distance (sourceCoefficient 30 84 3 1) v2528_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2528_mg : Scalar.QComplex := ((-93086177976257711355721 : Int)/10^30,(214018381231312557479 : Int)/10^30)
theorem v2528_mg_checked : Scalar.distance (sourceCoefficient 30 84 3 2) v2528_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2528_upper : Scalar.QComplex := ((999995000586686639656639356340 : Int)/10^30,(-3162088175966509779681652971 : Int)/10^30)
theorem v2528_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 30 84 5) 1) 14) v2528_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2528 : Material (30 : Basis) (84 : Basis) where
  plus := ![v2528_pa,v2528_pb,v2528_pg]
  minus := ![(Primitive.Addresses.material2528 1).one,v2528_mb,v2528_mg]
  upper := v2528_upper
  lower := (Primitive.Addresses.material2528 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2528_pa_checked.trans (by decide +kernel)
    · exact v2528_pb_checked.trans (by decide +kernel)
    · exact v2528_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 30 84 Primitive.Addresses.material2528
    · exact v2528_mb_checked.trans (by decide +kernel)
    · exact v2528_mg_checked.trans (by decide +kernel)
  upper_error := v2528_upper_checked
  lower_error := reuse_lower_error 30 84 Primitive.Addresses.material2528

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
