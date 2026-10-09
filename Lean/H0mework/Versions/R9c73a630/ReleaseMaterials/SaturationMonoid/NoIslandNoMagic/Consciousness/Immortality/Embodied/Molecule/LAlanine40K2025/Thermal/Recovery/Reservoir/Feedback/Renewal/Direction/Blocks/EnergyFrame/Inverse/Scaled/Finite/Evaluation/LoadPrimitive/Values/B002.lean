import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B001
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B002

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v33_pa : Scalar.QComplex := ((999971701031935745235382100333 : Int)/10^30,(7523106758309098163182288598 : Int)/10^30)
theorem v33_pa_checked : Scalar.distance (sourceCoefficient 0 34 1 0) v33_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v33_pb : Scalar.QComplex := ((3246015384662250036294710 : Int)/10^30,(-431460516254338091977896561 : Int)/10^30)
theorem v33_pb_checked : Scalar.distance (sourceCoefficient 0 34 1 1) v33_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v33_pg : Scalar.QComplex := ((-93083278479921120178405 : Int)/10^30,(-700295259051033851147 : Int)/10^30)
theorem v33_pg_checked : Scalar.distance (sourceCoefficient 0 34 1 2) v33_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v33_mb : Scalar.QComplex := ((2873683182755171006961342 : Int)/10^30,(-431463156766951028384507681 : Int)/10^30)
theorem v33_mb_checked : Scalar.distance (sourceCoefficient 0 34 3 1) v33_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v33_mg : Scalar.QComplex := ((-93083848144030859518774 : Int)/10^30,(-619968321286168584106 : Int)/10^30)
theorem v33_mg_checked : Scalar.distance (sourceCoefficient 0 34 3 2) v33_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v33_upper : Scalar.QComplex := ((999983195891325913347480322800 : Int)/10^30,(5797235114268264221464473999 : Int)/10^30)
theorem v33_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 34 5) 1) 14) v33_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material33 : Material (0 : Basis) (34 : Basis) where
  plus := ![v33_pa,v33_pb,v33_pg]
  minus := ![(Primitive.Addresses.material33 1).one,v33_mb,v33_mg]
  upper := v33_upper
  lower := (Primitive.Addresses.material33 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v33_pa_checked.trans (by decide +kernel)
    · exact v33_pb_checked.trans (by decide +kernel)
    · exact v33_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 34 Primitive.Addresses.material33
    · exact v33_mb_checked.trans (by decide +kernel)
    · exact v33_mg_checked.trans (by decide +kernel)
  upper_error := v33_upper_checked
  lower_error := reuse_lower_error 0 34 Primitive.Addresses.material33

def v34_pa : Scalar.QComplex := ((999972086115532479180372728014 : Int)/10^30,(7471746097807096466357659621 : Int)/10^30)
theorem v34_pa_checked : Scalar.distance (sourceCoefficient 0 35 1 0) v34_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v34_pb : Scalar.QComplex := ((3223854208343630410595981 : Int)/10^30,(-431460621901468265643819010 : Int)/10^30)
theorem v34_pb_checked : Scalar.distance (sourceCoefficient 0 35 1 1) v34_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v34_pg : Scalar.QComplex := ((-93083307799026187642714 : Int)/10^30,(-695514256322947299134 : Int)/10^30)
theorem v34_pg_checked : Scalar.distance (sourceCoefficient 0 35 1 2) v34_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v34_mb : Scalar.QComplex := ((2851521923519454970714330 : Int)/10^30,(-431463243289944804156907647 : Int)/10^30)
theorem v34_mb_checked : Scalar.distance (sourceCoefficient 0 35 3 1) v34_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v34_mg : Scalar.QComplex := ((-93083873337334984171132 : Int)/10^30,(-615187295037200660632 : Int)/10^30)
theorem v34_mg_checked : Scalar.distance (sourceCoefficient 0 35 3 2) v34_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v34_upper : Scalar.QComplex := ((999983492330508486778788825683 : Int)/10^30,(5745873865642579643589546952 : Int)/10^30)
theorem v34_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 35 5) 1) 14) v34_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material34 : Material (0 : Basis) (35 : Basis) where
  plus := ![v34_pa,v34_pb,v34_pg]
  minus := ![(Primitive.Addresses.material34 1).one,v34_mb,v34_mg]
  upper := v34_upper
  lower := (Primitive.Addresses.material34 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v34_pa_checked.trans (by decide +kernel)
    · exact v34_pb_checked.trans (by decide +kernel)
    · exact v34_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 35 Primitive.Addresses.material34
    · exact v34_mb_checked.trans (by decide +kernel)
    · exact v34_mg_checked.trans (by decide +kernel)
  upper_error := v34_upper_checked
  lower_error := reuse_lower_error 0 35 Primitive.Addresses.material34

def v35_pa : Scalar.QComplex := ((999972206615982172976930603755 : Int)/10^30,(7455601623172933703915444349 : Int)/10^30)
theorem v35_pa_checked : Scalar.distance (sourceCoefficient 0 36 1 0) v35_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v35_pb : Scalar.QComplex := ((3216888166444847644660665 : Int)/10^30,(-431460654796587587258743704 : Int)/10^30)
theorem v35_pb_checked : Scalar.distance (sourceCoefficient 0 36 1 1) v35_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v35_pg : Scalar.QComplex := ((-93083316955876192772573 : Int)/10^30,(-694011417912402001021 : Int)/10^30)
theorem v35_pg_checked : Scalar.distance (sourceCoefficient 0 36 1 2) v35_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v35_mb : Scalar.QComplex := ((2844555855827441534161277 : Int)/10^30,(-431463270173671457646587159 : Int)/10^30)
theorem v35_mb_checked : Scalar.distance (sourceCoefficient 0 36 3 1) v35_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v35_mg : Scalar.QComplex := ((-93083881197299716816066 : Int)/10^30,(-613684449284281640660 : Int)/10^30)
theorem v35_mg_checked : Scalar.distance (sourceCoefficient 0 36 3 2) v35_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v35_upper : Scalar.QComplex := ((999983584966880106043441369782 : Int)/10^30,(5729729207080870929432450953 : Int)/10^30)
theorem v35_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 36 5) 1) 14) v35_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material35 : Material (0 : Basis) (36 : Basis) where
  plus := ![v35_pa,v35_pb,v35_pg]
  minus := ![(Primitive.Addresses.material35 1).one,v35_mb,v35_mg]
  upper := v35_upper
  lower := (Primitive.Addresses.material35 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v35_pa_checked.trans (by decide +kernel)
    · exact v35_pb_checked.trans (by decide +kernel)
    · exact v35_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 36 Primitive.Addresses.material35
    · exact v35_mb_checked.trans (by decide +kernel)
    · exact v35_mg_checked.trans (by decide +kernel)
  upper_error := v35_upper_checked
  lower_error := reuse_lower_error 0 36 Primitive.Addresses.material35

def v36_pa : Scalar.QComplex := ((999972257991560106668768206381 : Int)/10^30,(7448707757776135450494556622 : Int)/10^30)
theorem v36_pa_checked : Scalar.distance (sourceCoefficient 0 37 1 0) v36_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v36_pb : Scalar.QComplex := ((3213913591264972477915346 : Int)/10^30,(-431460668797470529708014124 : Int)/10^30)
theorem v36_pb_checked : Scalar.distance (sourceCoefficient 0 37 1 1) v36_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v36_pg : Scalar.QComplex := ((-93083320857325412212711 : Int)/10^30,(-693369689657307392631 : Int)/10^30)
theorem v36_pg_checked : Scalar.distance (sourceCoefficient 0 37 1 2) v36_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v36_mb : Scalar.QComplex := ((2841581269673005248710925 : Int)/10^30,(-431463281607624776587902629 : Int)/10^30)
theorem v36_mb_checked : Scalar.distance (sourceCoefficient 0 37 3 1) v36_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v36_mg : Scalar.QComplex := ((-93083884544964901789410 : Int)/10^30,(-613042717901356828445 : Int)/10^30)
theorem v36_mg_checked : Scalar.distance (sourceCoefficient 0 37 3 2) v36_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v36_upper : Scalar.QComplex := ((999983624444195253556550065086 : Int)/10^30,(5722835263282088616697186533 : Int)/10^30)
theorem v36_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 37 5) 1) 14) v36_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material36 : Material (0 : Basis) (37 : Basis) where
  plus := ![v36_pa,v36_pb,v36_pg]
  minus := ![(Primitive.Addresses.material36 1).one,v36_mb,v36_mg]
  upper := v36_upper
  lower := (Primitive.Addresses.material36 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v36_pa_checked.trans (by decide +kernel)
    · exact v36_pb_checked.trans (by decide +kernel)
    · exact v36_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 37 Primitive.Addresses.material36
    · exact v36_mb_checked.trans (by decide +kernel)
    · exact v36_mg_checked.trans (by decide +kernel)
  upper_error := v36_upper_checked
  lower_error := reuse_lower_error 0 37 Primitive.Addresses.material36

def v37_pa : Scalar.QComplex := ((999972431282557667252108456977 : Int)/10^30,(7425407386163003016490044225 : Int)/10^30)
theorem v37_pa_checked : Scalar.distance (sourceCoefficient 0 38 1 0) v37_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v37_pb : Scalar.QComplex := ((3203859913112387445370370 : Int)/10^30,(-431460715916252441293483624 : Int)/10^30)
theorem v37_pb_checked : Scalar.distance (sourceCoefficient 0 38 1 1) v37_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v37_pg : Scalar.QComplex := ((-93083334005512858188465 : Int)/10^30,(-691200731370872103452 : Int)/10^30)
theorem v37_pg_checked : Scalar.distance (sourceCoefficient 0 38 1 2) v37_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v37_mb : Scalar.QComplex := ((2831527554602477429624578 : Int)/10^30,(-431463320050517698871783225 : Int)/10^30)
theorem v37_mb_checked : Scalar.distance (sourceCoefficient 0 38 3 1) v37_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v37_mg : Scalar.QComplex := ((-93083895821434137155358 : Int)/10^30,(-610873749076230242100 : Int)/10^30)
theorem v37_mg_checked : Scalar.distance (sourceCoefficient 0 38 3 2) v37_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v37_upper : Scalar.QComplex := ((999983757520607106489330297973 : Int)/10^30,(5699534627287581693463620387 : Int)/10^30)
theorem v37_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 38 5) 1) 14) v37_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material37 : Material (0 : Basis) (38 : Basis) where
  plus := ![v37_pa,v37_pb,v37_pg]
  minus := ![(Primitive.Addresses.material37 1).one,v37_mb,v37_mg]
  upper := v37_upper
  lower := (Primitive.Addresses.material37 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v37_pa_checked.trans (by decide +kernel)
    · exact v37_pb_checked.trans (by decide +kernel)
    · exact v37_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 38 Primitive.Addresses.material37
    · exact v37_mb_checked.trans (by decide +kernel)
    · exact v37_mg_checked.trans (by decide +kernel)
  upper_error := v37_upper_checked
  lower_error := reuse_lower_error 0 38 Primitive.Addresses.material37

def v38_pa : Scalar.QComplex := ((999972531563355181703937395398 : Int)/10^30,(7411890364449873710004392742 : Int)/10^30)
theorem v38_pa_checked : Scalar.distance (sourceCoefficient 0 39 1 0) v38_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v38_pb : Scalar.QComplex := ((3198027569295703783345567 : Int)/10^30,(-431460743107657407981329158 : Int)/10^30)
theorem v38_pb_checked : Scalar.distance (sourceCoefficient 0 39 1 1) v38_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v38_pg : Scalar.QComplex := ((-93083341606019773252517 : Int)/10^30,(-689942474381600110145 : Int)/10^30)
theorem v38_pg_checked : Scalar.distance (sourceCoefficient 0 39 1 2) v38_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v38_mb : Scalar.QComplex := ((2825695189492484090998168 : Int)/10^30,(-431463342208862506173250799 : Int)/10^30)
theorem v38_mb_checked : Scalar.distance (sourceCoefficient 0 39 3 1) v38_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v38_mg : Scalar.QComplex := ((-93083902336119110252711 : Int)/10^30,(-609615485996569677508 : Int)/10^30)
theorem v38_mg_checked : Scalar.distance (sourceCoefficient 0 39 3 2) v38_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v38_upper : Scalar.QComplex := ((999983834472102042242728022055 : Int)/10^30,(5686017452630909300716954287 : Int)/10^30)
theorem v38_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 39 5) 1) 14) v38_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material38 : Material (0 : Basis) (39 : Basis) where
  plus := ![v38_pa,v38_pb,v38_pg]
  minus := ![(Primitive.Addresses.material38 1).one,v38_mb,v38_mg]
  upper := v38_upper
  lower := (Primitive.Addresses.material38 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v38_pa_checked.trans (by decide +kernel)
    · exact v38_pb_checked.trans (by decide +kernel)
    · exact v38_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 39 Primitive.Addresses.material38
    · exact v38_mb_checked.trans (by decide +kernel)
    · exact v38_mg_checked.trans (by decide +kernel)
  upper_error := v38_upper_checked
  lower_error := reuse_lower_error 0 39 Primitive.Addresses.material38

def v39_pa : Scalar.QComplex := ((999972699817934178928991882493 : Int)/10^30,(7389155488396580969446064203 : Int)/10^30)
theorem v39_pa_checked : Scalar.distance (sourceCoefficient 0 40 1 0) v39_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v39_pb : Scalar.QComplex := ((3188217893077416037069873 : Int)/10^30,(-431460788604988735261096722 : Int)/10^30)
theorem v39_pb_checked : Scalar.distance (sourceCoefficient 0 40 1 1) v39_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v39_pg : Scalar.QComplex := ((-93083354344891305297868 : Int)/10^30,(-687826156415217089559 : Int)/10^30)
theorem v39_pg_checked : Scalar.distance (sourceCoefficient 0 40 1 2) v39_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v39_mb : Scalar.QComplex := ((2815885477664639313435343 : Int)/10^30,(-431463379240868127750970408 : Int)/10^30)
theorem v39_mb_checked : Scalar.distance (sourceCoefficient 0 40 3 1) v39_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v39_mg : Scalar.QComplex := ((-93083913248698809468379 : Int)/10^30,(-607499157825116161636 : Int)/10^30)
theorem v39_mg_checked : Scalar.distance (sourceCoefficient 0 40 3 2) v39_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v39_upper : Scalar.QComplex := ((999983963488096867897919765638 : Int)/10^30,(5663282320046404402356546871 : Int)/10^30)
theorem v39_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 40 5) 1) 14) v39_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material39 : Material (0 : Basis) (40 : Basis) where
  plus := ![v39_pa,v39_pb,v39_pg]
  minus := ![(Primitive.Addresses.material39 1).one,v39_mb,v39_mg]
  upper := v39_upper
  lower := (Primitive.Addresses.material39 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v39_pa_checked.trans (by decide +kernel)
    · exact v39_pb_checked.trans (by decide +kernel)
    · exact v39_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 40 Primitive.Addresses.material39
    · exact v39_mb_checked.trans (by decide +kernel)
    · exact v39_mg_checked.trans (by decide +kernel)
  upper_error := v39_upper_checked
  lower_error := reuse_lower_error 0 40 Primitive.Addresses.material39

def v40_pa : Scalar.QComplex := ((999972806737530395010301767594 : Int)/10^30,(7374671888679945777727271634 : Int)/10^30)
theorem v40_pa_checked : Scalar.distance (sourceCoefficient 0 41 1 0) v40_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v40_pb : Scalar.QComplex := ((3181968489506756463452554 : Int)/10^30,(-431460817434686299988519044 : Int)/10^30)
theorem v40_pb_checked : Scalar.distance (sourceCoefficient 0 41 1 1) v40_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v40_pg : Scalar.QComplex := ((-93083362431110532601074 : Int)/10^30,(-686477923798879273073 : Int)/10^30)
theorem v40_pg_checked : Scalar.distance (sourceCoefficient 0 41 1 2) v40_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v40_mb : Scalar.QComplex := ((2809636051542187744045414 : Int)/10^30,(-431463402677601139073631463 : Int)/10^30)
theorem v40_mb_checked : Scalar.distance (sourceCoefficient 0 41 3 1) v40_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v40_mg : Scalar.QComplex := ((-93083920171451000146001 : Int)/10^30,(-606150918732743962119 : Int)/10^30)
theorem v40_mg_checked : Scalar.distance (sourceCoefficient 0 41 3 2) v40_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v40_upper : Scalar.QComplex := ((999984045410154670790325202997 : Int)/10^30,(5648798557367866226471632630 : Int)/10^30)
theorem v40_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 41 5) 1) 14) v40_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material40 : Material (0 : Basis) (41 : Basis) where
  plus := ![v40_pa,v40_pb,v40_pg]
  minus := ![(Primitive.Addresses.material40 1).one,v40_mb,v40_mg]
  upper := v40_upper
  lower := (Primitive.Addresses.material40 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v40_pa_checked.trans (by decide +kernel)
    · exact v40_pb_checked.trans (by decide +kernel)
    · exact v40_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 41 Primitive.Addresses.material40
    · exact v40_mb_checked.trans (by decide +kernel)
    · exact v40_mg_checked.trans (by decide +kernel)
  upper_error := v40_upper_checked
  lower_error := reuse_lower_error 0 41 Primitive.Addresses.material40

def v41_pa : Scalar.QComplex := ((999972892832363216163936083584 : Int)/10^30,(7362988555948622648032438939 : Int)/10^30)
theorem v41_pa_checked : Scalar.distance (sourceCoefficient 0 42 1 0) v41_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v41_pb : Scalar.QComplex := ((3176927349198319990973775 : Int)/10^30,(-431460840602488463827132344 : Int)/10^30)
theorem v41_pb_checked : Scalar.distance (sourceCoefficient 0 42 1 1) v41_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v41_pg : Scalar.QComplex := ((-93083368937333954850641 : Int)/10^30,(-685390359226097591028 : Int)/10^30)
theorem v41_pg_checked : Scalar.distance (sourceCoefficient 0 42 1 2) v41_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v41_mb : Scalar.QComplex := ((2804594893118028371573657 : Int)/10^30,(-431463421495117634831205356 : Int)/10^30)
theorem v41_mb_checked : Scalar.distance (sourceCoefficient 0 42 3 1) v41_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v41_mg : Scalar.QComplex := ((-93083925739152755610705 : Int)/10^30,(-605063348950334490701 : Int)/10^30)
theorem v41_mg_checked : Scalar.distance (sourceCoefficient 0 42 3 2) v41_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v41_upper : Scalar.QComplex := ((999984111340486873206032611695 : Int)/10^30,(5637115093445623792323066130 : Int)/10^30)
theorem v41_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 42 5) 1) 14) v41_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material41 : Material (0 : Basis) (42 : Basis) where
  plus := ![v41_pa,v41_pb,v41_pg]
  minus := ![(Primitive.Addresses.material41 1).one,v41_mb,v41_mg]
  upper := v41_upper
  lower := (Primitive.Addresses.material41 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v41_pa_checked.trans (by decide +kernel)
    · exact v41_pb_checked.trans (by decide +kernel)
    · exact v41_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 42 Primitive.Addresses.material41
    · exact v41_mb_checked.trans (by decide +kernel)
    · exact v41_mg_checked.trans (by decide +kernel)
  upper_error := v41_upper_checked
  lower_error := reuse_lower_error 0 42 Primitive.Addresses.material41

def v42_pa : Scalar.QComplex := ((999973006675365062667796620493 : Int)/10^30,(7347511186129614685018279225 : Int)/10^30)
theorem v42_pa_checked : Scalar.distance (sourceCoefficient 0 43 1 0) v42_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v42_pb : Scalar.QComplex := ((3170249152884343874155849 : Int)/10^30,(-431460871172855777816680667 : Int)/10^30)
theorem v42_pb_checked : Scalar.distance (sourceCoefficient 0 43 1 1) v42_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v42_pg : Scalar.QComplex := ((-93083377533555376785604 : Int)/10^30,(-683949619744643903059 : Int)/10^30)
theorem v42_pg_checked : Scalar.distance (sourceCoefficient 0 43 1 2) v42_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v42_mb : Scalar.QComplex := ((2797916672909799797358405 : Int)/10^30,(-431463446302490921911175262 : Int)/10^30)
theorem v42_mb_checked : Scalar.distance (sourceCoefficient 0 43 3 1) v42_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v42_mg : Scalar.QComplex := ((-93083933092077692782503 : Int)/10^30,(-603622602587182029036 : Int)/10^30)
theorem v42_mg_checked : Scalar.distance (sourceCoefficient 0 43 3 2) v42_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v42_upper : Scalar.QComplex := ((999984198470782952345621210429 : Int)/10^30,(5621637550195646644533642868 : Int)/10^30)
theorem v42_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 43 5) 1) 14) v42_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material42 : Material (0 : Basis) (43 : Basis) where
  plus := ![v42_pa,v42_pb,v42_pg]
  minus := ![(Primitive.Addresses.material42 1).one,v42_mb,v42_mg]
  upper := v42_upper
  lower := (Primitive.Addresses.material42 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v42_pa_checked.trans (by decide +kernel)
    · exact v42_pb_checked.trans (by decide +kernel)
    · exact v42_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 43 Primitive.Addresses.material42
    · exact v42_mb_checked.trans (by decide +kernel)
    · exact v42_mg_checked.trans (by decide +kernel)
  upper_error := v42_upper_checked
  lower_error := reuse_lower_error 0 43 Primitive.Addresses.material42

def v43_pa : Scalar.QComplex := ((999973049683625280987602705565 : Int)/10^30,(7341655564645165737336788230 : Int)/10^30)
theorem v43_pa_checked : Scalar.distance (sourceCoefficient 0 44 1 0) v43_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v43_pb : Scalar.QComplex := ((3167722561546523013396807 : Int)/10^30,(-431460882702742144164444929 : Int)/10^30)
theorem v43_pb_checked : Scalar.distance (sourceCoefficient 0 44 1 1) v43_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v43_pg : Scalar.QComplex := ((-93083380779018079264290 : Int)/10^30,(-683404538440785842081 : Int)/10^30)
theorem v43_pg_checked : Scalar.distance (sourceCoefficient 0 44 1 2) v43_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v43_mb : Scalar.QComplex := ((2795390072562971715245575 : Int)/10^30,(-431463455652038464065544700 : Int)/10^30)
theorem v43_mb_checked : Scalar.distance (sourceCoefficient 0 44 3 1) v43_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v43_mg : Scalar.QComplex := ((-93083935867158571148197 : Int)/10^30,(-603077518685594506905 : Int)/10^30)
theorem v43_mg_checked : Scalar.distance (sourceCoefficient 0 44 3 2) v43_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v43_upper : Scalar.QComplex := ((999984231372707650586476781520 : Int)/10^30,(5615781863204102590389273548 : Int)/10^30)
theorem v43_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 44 5) 1) 14) v43_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material43 : Material (0 : Basis) (44 : Basis) where
  plus := ![v43_pa,v43_pb,v43_pg]
  minus := ![(Primitive.Addresses.material43 1).one,v43_mb,v43_mg]
  upper := v43_upper
  lower := (Primitive.Addresses.material43 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v43_pa_checked.trans (by decide +kernel)
    · exact v43_pb_checked.trans (by decide +kernel)
    · exact v43_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 44 Primitive.Addresses.material43
    · exact v43_mb_checked.trans (by decide +kernel)
    · exact v43_mg_checked.trans (by decide +kernel)
  upper_error := v43_upper_checked
  lower_error := reuse_lower_error 0 44 Primitive.Addresses.material43

def v44_pa : Scalar.QComplex := ((999973071067998926210574278126 : Int)/10^30,(7338742319687267803902201229 : Int)/10^30)
theorem v44_pa_checked : Scalar.distance (sourceCoefficient 0 45 1 0) v44_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v44_pb : Scalar.QComplex := ((3166465550758761221127471 : Int)/10^30,(-431460888431656067050799059 : Int)/10^30)
theorem v44_pb_checked : Scalar.distance (sourceCoefficient 0 45 1 1) v44_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v44_pg : Scalar.QComplex := ((-93083382392289128481813 : Int)/10^30,(-683133353673553638887 : Int)/10^30)
theorem v44_pg_checked : Scalar.distance (sourceCoefficient 0 45 1 2) v44_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v44_mb : Scalar.QComplex := ((2794133057299457792744940 : Int)/10^30,(-431463460296206557641277097 : Int)/10^30)
theorem v44_mb_checked : Scalar.distance (sourceCoefficient 0 45 3 1) v44_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v44_mg : Scalar.QComplex := ((-93083937246408779258309 : Int)/10^30,(-602806332627156529864 : Int)/10^30)
theorem v44_mg_checked : Scalar.distance (sourceCoefficient 0 45 3 2) v44_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v44_upper : Scalar.QComplex := ((999984247729052936483135377822 : Int)/10^30,(5612868585677651871519686849 : Int)/10^30)
theorem v44_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 45 5) 1) 14) v44_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material44 : Material (0 : Basis) (45 : Basis) where
  plus := ![v44_pa,v44_pb,v44_pg]
  minus := ![(Primitive.Addresses.material44 1).one,v44_mb,v44_mg]
  upper := v44_upper
  lower := (Primitive.Addresses.material44 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v44_pa_checked.trans (by decide +kernel)
    · exact v44_pb_checked.trans (by decide +kernel)
    · exact v44_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 45 Primitive.Addresses.material44
    · exact v44_mb_checked.trans (by decide +kernel)
    · exact v44_mg_checked.trans (by decide +kernel)
  upper_error := v44_upper_checked
  lower_error := reuse_lower_error 0 45 Primitive.Addresses.material44

def v45_pa : Scalar.QComplex := ((999973191027072669195796818851 : Int)/10^30,(7322378516140243213995675305 : Int)/10^30)
theorem v45_pa_checked : Scalar.distance (sourceCoefficient 0 46 1 0) v45_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v45_pb : Scalar.QComplex := ((3159404875372663554202387 : Int)/10^30,(-431460920520430488123156792 : Int)/10^30)
theorem v45_pb_checked : Scalar.distance (sourceCoefficient 0 46 1 1) v45_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v45_pg : Scalar.QComplex := ((-93083391436961532765762 : Int)/10^30,(-681610098934169131238 : Int)/10^30)
theorem v45_pg_checked : Scalar.distance (sourceCoefficient 0 46 1 2) v45_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v45_mb : Scalar.QComplex := ((2787072356851205160235528 : Int)/10^30,(-431463486291924173408739158 : Int)/10^30)
theorem v45_mb_checked : Scalar.distance (sourceCoefficient 0 46 3 1) v45_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v45_mg : Scalar.QComplex := ((-93083944976577580555260 : Int)/10^30,(-601283070649804449895 : Int)/10^30)
theorem v45_mg_checked : Scalar.distance (sourceCoefficient 0 46 3 2) v45_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v45_upper : Scalar.QComplex := ((999984339445507605016367781241 : Int)/10^30,(5596504599464111759279791026 : Int)/10^30)
theorem v45_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 46 5) 1) 14) v45_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material45 : Material (0 : Basis) (46 : Basis) where
  plus := ![v45_pa,v45_pb,v45_pg]
  minus := ![(Primitive.Addresses.material45 1).one,v45_mb,v45_mg]
  upper := v45_upper
  lower := (Primitive.Addresses.material45 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v45_pa_checked.trans (by decide +kernel)
    · exact v45_pb_checked.trans (by decide +kernel)
    · exact v45_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 46 Primitive.Addresses.material45
    · exact v45_mb_checked.trans (by decide +kernel)
    · exact v45_mg_checked.trans (by decide +kernel)
  upper_error := v45_upper_checked
  lower_error := reuse_lower_error 0 46 Primitive.Addresses.material45

def v46_pa : Scalar.QComplex := ((999973219855158074703505381535 : Int)/10^30,(7318440578954838961750577755 : Int)/10^30)
theorem v46_pa_checked : Scalar.distance (sourceCoefficient 0 47 1 0) v46_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v46_pb : Scalar.QComplex := ((3157705729132429553153830 : Int)/10^30,(-431460928219571793129884430 : Int)/10^30)
theorem v46_pb_checked : Scalar.distance (sourceCoefficient 0 47 1 1) v46_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v46_pg : Scalar.QComplex := ((-93083393609213759501848 : Int)/10^30,(-681243528816869843208 : Int)/10^30)
theorem v46_pg_checked : Scalar.distance (sourceCoefficient 0 47 1 2) v46_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v46_mb : Scalar.QComplex := ((2785373204599628769476862 : Int)/10^30,(-431463492524775933057203181 : Int)/10^30)
theorem v46_mb_checked : Scalar.distance (sourceCoefficient 0 47 3 1) v46_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v46_mg : Scalar.QComplex := ((-93083946832495496938494 : Int)/10^30,(-600916498794440132552 : Int)/10^30)
theorem v46_mg_checked : Scalar.distance (sourceCoefficient 0 47 3 2) v46_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v46_upper : Scalar.QComplex := ((999984361477027739340310723413 : Int)/10^30,(5592566618389142215670240031 : Int)/10^30)
theorem v46_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 47 5) 1) 14) v46_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material46 : Material (0 : Basis) (47 : Basis) where
  plus := ![v46_pa,v46_pb,v46_pg]
  minus := ![(Primitive.Addresses.material46 1).one,v46_mb,v46_mg]
  upper := v46_upper
  lower := (Primitive.Addresses.material46 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v46_pa_checked.trans (by decide +kernel)
    · exact v46_pb_checked.trans (by decide +kernel)
    · exact v46_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 47 Primitive.Addresses.material46
    · exact v46_mb_checked.trans (by decide +kernel)
    · exact v46_mg_checked.trans (by decide +kernel)
  upper_error := v46_upper_checked
  lower_error := reuse_lower_error 0 47 Primitive.Addresses.material46

def v47_pa : Scalar.QComplex := ((999973420227930760104022816217 : Int)/10^30,(7291010742976349449199094261 : Int)/10^30)
theorem v47_pa_checked : Scalar.distance (sourceCoefficient 0 48 1 0) v47_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v47_pb : Scalar.QComplex := ((3145870268540430685810830 : Int)/10^30,(-431460981600687482696282714 : Int)/10^30)
theorem v47_pb_checked : Scalar.distance (sourceCoefficient 0 48 1 1) v47_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v47_pg : Scalar.QComplex := ((-93083408693386597395180 : Int)/10^30,(-678690172206422680663 : Int)/10^30)
theorem v47_pg_checked : Scalar.distance (sourceCoefficient 0 48 1 2) v47_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v47_mb : Scalar.QComplex := ((2773537702349014143912354 : Int)/10^30,(-431463535692402304856911570 : Int)/10^30)
theorem v47_mb_checked : Scalar.distance (sourceCoefficient 0 48 3 1) v47_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v47_mg : Scalar.QComplex := ((-93083959713230962401770 : Int)/10^30,(-598363130117762537062 : Int)/10^30)
theorem v47_mg_checked : Scalar.distance (sourceCoefficient 0 48 3 2) v47_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v47_upper : Scalar.QComplex := ((999984514508093509441989023901 : Int)/10^30,(5565136477438943279142736590 : Int)/10^30)
theorem v47_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 48 5) 1) 14) v47_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material47 : Material (0 : Basis) (48 : Basis) where
  plus := ![v47_pa,v47_pb,v47_pg]
  minus := ![(Primitive.Addresses.material47 1).one,v47_mb,v47_mg]
  upper := v47_upper
  lower := (Primitive.Addresses.material47 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v47_pa_checked.trans (by decide +kernel)
    · exact v47_pb_checked.trans (by decide +kernel)
    · exact v47_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 48 Primitive.Addresses.material47
    · exact v47_mb_checked.trans (by decide +kernel)
    · exact v47_mg_checked.trans (by decide +kernel)
  upper_error := v47_upper_checked
  lower_error := reuse_lower_error 0 48 Primitive.Addresses.material47

def v48_pa : Scalar.QComplex := ((999973580667186995703513487118 : Int)/10^30,(7268972942917197892265240451 : Int)/10^30)
theorem v48_pa_checked : Scalar.distance (sourceCoefficient 0 49 1 0) v48_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v48_pb : Scalar.QComplex := ((3136361371224651948349756 : Int)/10^30,(-431461024174772416120173434 : Int)/10^30)
theorem v48_pb_checked : Scalar.distance (sourceCoefficient 0 49 1 1) v48_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v48_pg : Scalar.QComplex := ((-93083420753179008314861 : Int)/10^30,(-676638743233187039770 : Int)/10^30)
theorem v48_pg_checked : Scalar.distance (sourceCoefficient 0 49 1 2) v48_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v48_mb : Scalar.QComplex := ((2764028771834314623252542 : Int)/10^30,(-431463570060721267323363974 : Int)/10^30)
theorem v48_mb_checked : Scalar.distance (sourceCoefficient 0 49 3 1) v48_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v48_mg : Scalar.QComplex := ((-93083970002728071938387 : Int)/10^30,(-596311691501309960104 : Int)/10^30)
theorem v48_mg_checked : Scalar.distance (sourceCoefficient 0 49 3 2) v48_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v48_upper : Scalar.QComplex := ((999984636911867141124302562048 : Int)/10^30,(5543098433298904841455037726 : Int)/10^30)
theorem v48_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 49 5) 1) 14) v48_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material48 : Material (0 : Basis) (49 : Basis) where
  plus := ![v48_pa,v48_pb,v48_pg]
  minus := ![(Primitive.Addresses.material48 1).one,v48_mb,v48_mg]
  upper := v48_upper
  lower := (Primitive.Addresses.material48 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v48_pa_checked.trans (by decide +kernel)
    · exact v48_pb_checked.trans (by decide +kernel)
    · exact v48_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 49 Primitive.Addresses.material48
    · exact v48_mb_checked.trans (by decide +kernel)
    · exact v48_mg_checked.trans (by decide +kernel)
  upper_error := v48_upper_checked
  lower_error := reuse_lower_error 0 49 Primitive.Addresses.material48

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
