import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B189
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B190

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4545_pa : Scalar.QComplex := ((999997781680890853737738195620 : Int)/10^30,(-2106331715887327781216736703 : Int)/10^30)
theorem v4545_pa_checked : Scalar.distance (sourceCoefficient 77 80 1 0) v4545_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4545_pb : Scalar.QComplex := ((-908834787024969809963048 : Int)/10^30,(-431476563774065165998017247 : Int)/10^30)
theorem v4545_pb_checked : Scalar.distance (sourceCoefficient 77 80 1 1) v4545_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4545_pg : Scalar.QComplex := ((-93086223393829369723671 : Int)/10^30,(196070899594419046611 : Int)/10^30)
theorem v4545_pg_checked : Scalar.distance (sourceCoefficient 77 80 1 2) v4545_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4545_mb : Scalar.QComplex := ((-1281179290178214892979472 : Int)/10^30,(-431475618832132216564903844 : Int)/10^30)
theorem v4545_mb_checked : Scalar.distance (sourceCoefficient 77 80 3 1) v4545_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4545_mg : Scalar.QComplex := ((-93086019533218505150554 : Int)/10^30,(276400044929266313275 : Int)/10^30)
theorem v4545_mg_checked : Scalar.distance (sourceCoefficient 77 80 3 2) v4545_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4545_upper : Scalar.QComplex := ((999992656964206330227429818119 : Int)/10^30,(-3832234030844786236108776635 : Int)/10^30)
theorem v4545_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 77 80 5) 1) 14) v4545_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4545 : Material (77 : Basis) (80 : Basis) where
  plus := ![v4545_pa,v4545_pb,v4545_pg]
  minus := ![(Primitive.Addresses.material4545 1).one,v4545_mb,v4545_mg]
  upper := v4545_upper
  lower := (Primitive.Addresses.material4545 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4545_pa_checked.trans (by decide +kernel)
    · exact v4545_pb_checked.trans (by decide +kernel)
    · exact v4545_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 77 80 Primitive.Addresses.material4545
    · exact v4545_mb_checked.trans (by decide +kernel)
    · exact v4545_mg_checked.trans (by decide +kernel)
  upper_error := v4545_upper_checked
  lower_error := reuse_lower_error 77 80 Primitive.Addresses.material4545

def v4546_pa : Scalar.QComplex := ((999997726083241787944415993053 : Int)/10^30,(-2132563796402510414330372324 : Int)/10^30)
theorem v4546_pa_checked : Scalar.distance (sourceCoefficient 77 81 1 0) v4546_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4546_pb : Scalar.QComplex := ((-920153339734780126844981 : Int)/10^30,(-431476539616265237582952731 : Int)/10^30)
theorem v4546_pb_checked : Scalar.distance (sourceCoefficient 77 81 1 1) v4546_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4546_pg : Scalar.QComplex := ((-93086218200249011019961 : Int)/10^30,(198512750279345070310 : Int)/10^30)
theorem v4546_pg_checked : Scalar.distance (sourceCoefficient 77 81 1 2) v4546_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4546_mb : Scalar.QComplex := ((-1292497817826517441282985 : Int)/10^30,(-431475584906940063327061762 : Int)/10^30)
theorem v4546_mb_checked : Scalar.distance (sourceCoefficient 77 81 3 1) v4546_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4546_mg : Scalar.QComplex := ((-93086012232432916035328 : Int)/10^30,(278841890223153789501 : Int)/10^30)
theorem v4546_mg_checked : Scalar.distance (sourceCoefficient 77 81 3 2) v4546_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4546_upper : Scalar.QComplex := ((999992556092448857150913308282 : Int)/10^30,(-3858465976333867870258444067 : Int)/10^30)
theorem v4546_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 77 81 5) 1) 14) v4546_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4546 : Material (77 : Basis) (81 : Basis) where
  plus := ![v4546_pa,v4546_pb,v4546_pg]
  minus := ![(Primitive.Addresses.material4546 1).one,v4546_mb,v4546_mg]
  upper := v4546_upper
  lower := (Primitive.Addresses.material4546 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4546_pa_checked.trans (by decide +kernel)
    · exact v4546_pb_checked.trans (by decide +kernel)
    · exact v4546_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 77 81 Primitive.Addresses.material4546
    · exact v4546_mb_checked.trans (by decide +kernel)
    · exact v4546_mg_checked.trans (by decide +kernel)
  upper_error := v4546_upper_checked
  lower_error := reuse_lower_error 77 81 Primitive.Addresses.material4546

def v4547_pa : Scalar.QComplex := ((999997704835601261260749188361 : Int)/10^30,(-2142504032597806165413892114 : Int)/10^30)
theorem v4547_pa_checked : Scalar.distance (sourceCoefficient 77 82 1 0) v4547_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4547_pb : Scalar.QComplex := ((-924442328011764837861083 : Int)/10^30,(-431476530358616178332911323 : Int)/10^30)
theorem v4547_pb_checked : Scalar.distance (sourceCoefficient 77 82 1 1) v4547_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4547_pg : Scalar.QComplex := ((-93086216212698597853527 : Int)/10^30,(199438051358093260393 : Int)/10^30)
theorem v4547_pg_checked : Scalar.distance (sourceCoefficient 77 82 1 2) v4547_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4547_mb : Scalar.QComplex := ((-1296786796517581611232978 : Int)/10^30,(-431475571948090736946285167 : Int)/10^30)
theorem v4547_mb_checked : Scalar.distance (sourceCoefficient 77 82 3 1) v4547_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4547_mg : Scalar.QComplex := ((-93086009446390085978634 : Int)/10^30,(279767189242203609003 : Int)/10^30)
theorem v4547_mg_checked : Scalar.distance (sourceCoefficient 77 82 3 2) v4547_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4547_upper : Scalar.QComplex := ((999992517688894074434808766470 : Int)/10^30,(-3868406161052849492451449969 : Int)/10^30)
theorem v4547_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 77 82 5) 1) 14) v4547_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4547 : Material (77 : Basis) (82 : Basis) where
  plus := ![v4547_pa,v4547_pb,v4547_pg]
  minus := ![(Primitive.Addresses.material4547 1).one,v4547_mb,v4547_mg]
  upper := v4547_upper
  lower := (Primitive.Addresses.material4547 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4547_pa_checked.trans (by decide +kernel)
    · exact v4547_pb_checked.trans (by decide +kernel)
    · exact v4547_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 77 82 Primitive.Addresses.material4547
    · exact v4547_mb_checked.trans (by decide +kernel)
    · exact v4547_mg_checked.trans (by decide +kernel)
  upper_error := v4547_upper_checked
  lower_error := reuse_lower_error 77 82 Primitive.Addresses.material4547

def v4548_pa : Scalar.QComplex := ((999997675672722917015861532428 : Int)/10^30,(-2156072622076695561539841973 : Int)/10^30)
theorem v4548_pa_checked : Scalar.distance (sourceCoefficient 77 83 1 0) v4548_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4548_pb : Scalar.QComplex := ((-930296869045453261535260 : Int)/10^30,(-431476517630013494267410486 : Int)/10^30)
theorem v4548_pb_checked : Scalar.distance (sourceCoefficient 77 83 1 1) v4548_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4548_pg : Scalar.QComplex := ((-93086213482337935818096 : Int)/10^30,(200701102877103361274 : Int)/10^30)
theorem v4548_pg_checked : Scalar.distance (sourceCoefficient 77 83 1 2) v4548_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4548_mb : Scalar.QComplex := ((-1302641324387146000957095 : Int)/10^30,(-431475554167287558988122259 : Int)/10^30)
theorem v4548_mb_checked : Scalar.distance (sourceCoefficient 77 83 3 1) v4548_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4548_mg : Scalar.QComplex := ((-93086005626073865404264 : Int)/10^30,(281030237934743624593 : Int)/10^30)
theorem v4548_mg_checked : Scalar.distance (sourceCoefficient 77 83 3 2) v4548_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4548_upper : Scalar.QComplex := ((999992465107904657130410141179 : Int)/10^30,(-3881974679990436351745833675 : Int)/10^30)
theorem v4548_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 77 83 5) 1) 14) v4548_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4548 : Material (77 : Basis) (83 : Basis) where
  plus := ![v4548_pa,v4548_pb,v4548_pg]
  minus := ![(Primitive.Addresses.material4548 1).one,v4548_mb,v4548_mg]
  upper := v4548_upper
  lower := (Primitive.Addresses.material4548 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4548_pa_checked.trans (by decide +kernel)
    · exact v4548_pb_checked.trans (by decide +kernel)
    · exact v4548_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 77 83 Primitive.Addresses.material4548
    · exact v4548_mb_checked.trans (by decide +kernel)
    · exact v4548_mg_checked.trans (by decide +kernel)
  upper_error := v4548_upper_checked
  lower_error := reuse_lower_error 77 83 Primitive.Addresses.material4548

def v4549_pa : Scalar.QComplex := ((999997599292988532291487187060 : Int)/10^30,(-2191211596250180060508167698 : Int)/10^30)
theorem v4549_pa_checked : Scalar.distance (sourceCoefficient 77 84 1 0) v4549_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4549_pb : Scalar.QComplex := ((-945458545400393170582402 : Int)/10^30,(-431476484174049324846303157 : Int)/10^30)
theorem v4549_pb_checked : Scalar.distance (sourceCoefficient 77 84 1 1) v4549_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4549_pg : Scalar.QComplex := ((-93086206318505252529467 : Int)/10^30,(203972064413210671797 : Int)/10^30)
theorem v4549_pg_checked : Scalar.distance (sourceCoefficient 77 84 1 2) v4549_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4549_mb : Scalar.QComplex := ((-1317802966225710602700310 : Int)/10^30,(-431475507627492008992546465 : Int)/10^30)
theorem v4549_mb_checked : Scalar.distance (sourceCoefficient 77 84 3 1) v4549_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4549_mg : Scalar.QComplex := ((-93085995639551362516198 : Int)/10^30,(284301192070857506265 : Int)/10^30)
theorem v4549_mg_checked : Scalar.distance (sourceCoefficient 77 84 3 2) v4549_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4549_upper : Scalar.QComplex := ((999992328081602390449388323125 : Int)/10^30,(-3917113470004054100513333056 : Int)/10^30)
theorem v4549_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 77 84 5) 1) 14) v4549_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4549 : Material (77 : Basis) (84 : Basis) where
  plus := ![v4549_pa,v4549_pb,v4549_pg]
  minus := ![(Primitive.Addresses.material4549 1).one,v4549_mb,v4549_mg]
  upper := v4549_upper
  lower := (Primitive.Addresses.material4549 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4549_pa_checked.trans (by decide +kernel)
    · exact v4549_pb_checked.trans (by decide +kernel)
    · exact v4549_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 77 84 Primitive.Addresses.material4549
    · exact v4549_mb_checked.trans (by decide +kernel)
    · exact v4549_mg_checked.trans (by decide +kernel)
  upper_error := v4549_upper_checked
  lower_error := reuse_lower_error 77 84 Primitive.Addresses.material4549

def v4550_pa : Scalar.QComplex := ((999997422937790874533977909317 : Int)/10^30,(-2270268216973779145002563597 : Int)/10^30)
theorem v4550_pa_checked : Scalar.distance (sourceCoefficient 77 85 1 0) v4550_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4550_pb : Scalar.QComplex := ((-979569696024889282177137 : Int)/10^30,(-431476406306998981433268241 : Int)/10^30)
theorem v4550_pb_checked : Scalar.distance (sourceCoefficient 77 85 1 1) v4550_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4550_pg : Scalar.QComplex := ((-93086189710896528886652 : Int)/10^30,(211331162553392635523 : Int)/10^30)
theorem v4550_pg_checked : Scalar.distance (sourceCoefficient 77 85 1 2) v4550_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4550_mb : Scalar.QComplex := ((-1351914036953308935593577 : Int)/10^30,(-431475400324083979294559394 : Int)/10^30)
theorem v4550_mb_checked : Scalar.distance (sourceCoefficient 77 85 3 1) v4550_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4550_mg : Scalar.QComplex := ((-93085972681378569144630 : Int)/10^30,(291660273139292555429 : Int)/10^30)
theorem v4550_mg_checked : Scalar.distance (sourceCoefficient 77 85 3 2) v4550_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4550_upper : Scalar.QComplex := ((999992015282111984718396855299 : Int)/10^30,(-3996169668609030921494317265 : Int)/10^30)
theorem v4550_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 77 85 5) 1) 14) v4550_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4550 : Material (77 : Basis) (85 : Basis) where
  plus := ![v4550_pa,v4550_pb,v4550_pg]
  minus := ![(Primitive.Addresses.material4550 1).one,v4550_mb,v4550_mg]
  upper := v4550_upper
  lower := (Primitive.Addresses.material4550 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4550_pa_checked.trans (by decide +kernel)
    · exact v4550_pb_checked.trans (by decide +kernel)
    · exact v4550_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 77 85 Primitive.Addresses.material4550
    · exact v4550_mb_checked.trans (by decide +kernel)
    · exact v4550_mg_checked.trans (by decide +kernel)
  upper_error := v4550_upper_checked
  lower_error := reuse_lower_error 77 85 Primitive.Addresses.material4550

def v4551_pa : Scalar.QComplex := ((999997389720381270554299267397 : Int)/10^30,(-2284852823246872382043104714 : Int)/10^30)
theorem v4551_pa_checked : Scalar.distance (sourceCoefficient 77 86 1 0) v4551_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4551_pb : Scalar.QComplex := ((-985862624772208327907209 : Int)/10^30,(-431476391548994056725552664 : Int)/10^30)
theorem v4551_pb_checked : Scalar.distance (sourceCoefficient 77 86 1 1) v4551_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4551_pg : Scalar.QComplex := ((-93086186572914574969901 : Int)/10^30,(212688791373626225348 : Int)/10^30)
theorem v4551_pg_checked : Scalar.distance (sourceCoefficient 77 86 1 2) v4551_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4551_mb : Scalar.QComplex := ((-1358206950621989433490358 : Int)/10^30,(-431475380135570463719838290 : Int)/10^30)
theorem v4551_mb_checked : Scalar.distance (sourceCoefficient 77 86 3 1) v4551_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4551_mg : Scalar.QComplex := ((-93085968371825257112626 : Int)/10^30,(293017898746081792009 : Int)/10^30)
theorem v4551_mg_checked : Scalar.distance (sourceCoefficient 77 86 3 2) v4551_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4551_upper : Scalar.QComplex := ((999991956893044531954969995714 : Int)/10^30,(-4010754195829830826353527596 : Int)/10^30)
theorem v4551_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 77 86 5) 1) 14) v4551_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4551 : Material (77 : Basis) (86 : Basis) where
  plus := ![v4551_pa,v4551_pb,v4551_pg]
  minus := ![(Primitive.Addresses.material4551 1).one,v4551_mb,v4551_mg]
  upper := v4551_upper
  lower := (Primitive.Addresses.material4551 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4551_pa_checked.trans (by decide +kernel)
    · exact v4551_pb_checked.trans (by decide +kernel)
    · exact v4551_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 77 86 Primitive.Addresses.material4551
    · exact v4551_mb_checked.trans (by decide +kernel)
    · exact v4551_mg_checked.trans (by decide +kernel)
  upper_error := v4551_upper_checked
  lower_error := reuse_lower_error 77 86 Primitive.Addresses.material4551

def v4552_pa : Scalar.QComplex := ((999997387513303599568123603994 : Int)/10^30,(-2285818577165328071555514948 : Int)/10^30)
theorem v4552_pa_checked : Scalar.distance (sourceCoefficient 77 87 1 0) v4552_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4552_pb : Scalar.QComplex := ((-986279325808910603443872 : Int)/10^30,(-431476390567438210693810683 : Int)/10^30)
theorem v4552_pb_checked : Scalar.distance (sourceCoefficient 77 87 1 1) v4552_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4552_pg : Scalar.QComplex := ((-93086186364310258825534 : Int)/10^30,(212778689950511012317 : Int)/10^30)
theorem v4552_pg_checked : Scalar.distance (sourceCoefficient 77 87 1 2) v4552_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4552_mb : Scalar.QComplex := ((-1358623650656496381393433 : Int)/10^30,(-431475378794420756010143371 : Int)/10^30)
theorem v4552_mb_checked : Scalar.distance (sourceCoefficient 77 87 3 1) v4552_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4552_mg : Scalar.QComplex := ((-93085968085642595671210 : Int)/10^30,(293107797109477100593 : Int)/10^30)
theorem v4552_mg_checked : Scalar.distance (sourceCoefficient 77 87 3 2) v4552_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4552_upper : Scalar.QComplex := ((999991953019166497408294534243 : Int)/10^30,(-4011719944500693664150661058 : Int)/10^30)
theorem v4552_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 77 87 5) 1) 14) v4552_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4552 : Material (77 : Basis) (87 : Basis) where
  plus := ![v4552_pa,v4552_pb,v4552_pg]
  minus := ![(Primitive.Addresses.material4552 1).one,v4552_mb,v4552_mg]
  upper := v4552_upper
  lower := (Primitive.Addresses.material4552 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4552_pa_checked.trans (by decide +kernel)
    · exact v4552_pb_checked.trans (by decide +kernel)
    · exact v4552_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 77 87 Primitive.Addresses.material4552
    · exact v4552_mb_checked.trans (by decide +kernel)
    · exact v4552_mg_checked.trans (by decide +kernel)
  upper_error := v4552_upper_checked
  lower_error := reuse_lower_error 77 87 Primitive.Addresses.material4552

def v4553_pa : Scalar.QComplex := ((999997360563862351586515458913 : Int)/10^30,(-2297578139840667583275764567 : Int)/10^30)
theorem v4553_pa_checked : Scalar.distance (sourceCoefficient 77 88 1 0) v4553_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4553_pb : Scalar.QComplex := ((-991353311879357419871100 : Int)/10^30,(-431476378572416711021741566 : Int)/10^30)
theorem v4553_pb_checked : Scalar.distance (sourceCoefficient 77 88 1 1) v4553_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4553_pg : Scalar.QComplex := ((-93086183816101026906312 : Int)/10^30,(213873345562101009197 : Int)/10^30)
theorem v4553_pg_checked : Scalar.distance (sourceCoefficient 77 88 1 2) v4553_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4553_mb : Scalar.QComplex := ((-1363697624486502972671021 : Int)/10^30,(-431475362420782267686584447 : Int)/10^30)
theorem v4553_mb_checked : Scalar.distance (sourceCoefficient 77 88 3 1) v4553_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4553_mg : Scalar.QComplex := ((-93085964592795821223166 : Int)/10^30,(294202450114486984982 : Int)/10^30)
theorem v4553_mg_checked : Scalar.distance (sourceCoefficient 77 88 3 2) v4553_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4553_upper : Scalar.QComplex := ((999991905773827029010096881707 : Int)/10^30,(-4023479443149255186416637868 : Int)/10^30)
theorem v4553_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 77 88 5) 1) 14) v4553_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4553 : Material (77 : Basis) (88 : Basis) where
  plus := ![v4553_pa,v4553_pb,v4553_pg]
  minus := ![(Primitive.Addresses.material4553 1).one,v4553_mb,v4553_mg]
  upper := v4553_upper
  lower := (Primitive.Addresses.material4553 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4553_pa_checked.trans (by decide +kernel)
    · exact v4553_pb_checked.trans (by decide +kernel)
    · exact v4553_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 77 88 Primitive.Addresses.material4553
    · exact v4553_mb_checked.trans (by decide +kernel)
    · exact v4553_mg_checked.trans (by decide +kernel)
  upper_error := v4553_upper_checked
  lower_error := reuse_lower_error 77 88 Primitive.Addresses.material4553

def v4554_pa : Scalar.QComplex := ((999997323467579007202558761414 : Int)/10^30,(-2313667581602809737763342973 : Int)/10^30)
theorem v4554_pa_checked : Scalar.distance (sourceCoefficient 77 89 1 0) v4554_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4554_pb : Scalar.QComplex := ((-998295543031579798776964 : Int)/10^30,(-431476362031929680867901515 : Int)/10^30)
theorem v4554_pb_checked : Scalar.distance (sourceCoefficient 77 89 1 1) v4554_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4554_pg : Scalar.QComplex := ((-93086180305308569831052 : Int)/10^30,(215371054115235258980 : Int)/10^30)
theorem v4554_pg_checked : Scalar.distance (sourceCoefficient 77 89 1 2) v4554_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4554_mb : Scalar.QComplex := ((-1370639838780120066826115 : Int)/10^30,(-431475339889468578428460945 : Int)/10^30)
theorem v4554_mb_checked : Scalar.distance (sourceCoefficient 77 89 3 1) v4554_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4554_mg : Scalar.QComplex := ((-93085959789549644310745 : Int)/10^30,(295700155080300121538 : Int)/10^30)
theorem v4554_mg_checked : Scalar.distance (sourceCoefficient 77 89 3 2) v4554_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4554_upper : Scalar.QComplex := ((999991840908682076479901746666 : Int)/10^30,(-4039568796923244130917651606 : Int)/10^30)
theorem v4554_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 77 89 5) 1) 14) v4554_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4554 : Material (77 : Basis) (89 : Basis) where
  plus := ![v4554_pa,v4554_pb,v4554_pg]
  minus := ![(Primitive.Addresses.material4554 1).one,v4554_mb,v4554_mg]
  upper := v4554_upper
  lower := (Primitive.Addresses.material4554 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4554_pa_checked.trans (by decide +kernel)
    · exact v4554_pb_checked.trans (by decide +kernel)
    · exact v4554_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 77 89 Primitive.Addresses.material4554
    · exact v4554_mb_checked.trans (by decide +kernel)
    · exact v4554_mg_checked.trans (by decide +kernel)
  upper_error := v4554_upper_checked
  lower_error := reuse_lower_error 77 89 Primitive.Addresses.material4554

def v4555_pa : Scalar.QComplex := ((999997262499386145563334204733 : Int)/10^30,(-2339870452353989293003744173 : Int)/10^30)
theorem v4555_pa_checked : Scalar.distance (sourceCoefficient 77 90 1 0) v4555_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4555_pb : Scalar.QComplex := ((-1009601490416418433293399 : Int)/10^30,(-431476334775725723510557494 : Int)/10^30)
theorem v4555_pb_checked : Scalar.distance (sourceCoefficient 77 90 1 1) v4555_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4555_pg : Scalar.QComplex := ((-93086174527542899492756 : Int)/10^30,(217810185555180860851 : Int)/10^30)
theorem v4555_pg_checked : Scalar.distance (sourceCoefficient 77 90 1 2) v4555_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4555_mb : Scalar.QComplex := ((-1381945758434361341302947 : Int)/10^30,(-431475302876751377653563410 : Int)/10^30)
theorem v4555_mb_checked : Scalar.distance (sourceCoefficient 77 90 3 1) v4555_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4555_mg : Scalar.QComplex := ((-93085951906925547027678 : Int)/10^30,(298139280626094061907 : Int)/10^30)
theorem v4555_mg_checked : Scalar.distance (sourceCoefficient 77 90 3 2) v4555_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4555_upper : Scalar.QComplex := ((999991734716802209131820252422 : Int)/10^30,(-4065771523422755819754000217 : Int)/10^30)
theorem v4555_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 77 90 5) 1) 14) v4555_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4555 : Material (77 : Basis) (90 : Basis) where
  plus := ![v4555_pa,v4555_pb,v4555_pg]
  minus := ![(Primitive.Addresses.material4555 1).one,v4555_mb,v4555_mg]
  upper := v4555_upper
  lower := (Primitive.Addresses.material4555 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4555_pa_checked.trans (by decide +kernel)
    · exact v4555_pb_checked.trans (by decide +kernel)
    · exact v4555_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 77 90 Primitive.Addresses.material4555
    · exact v4555_mb_checked.trans (by decide +kernel)
    · exact v4555_mg_checked.trans (by decide +kernel)
  upper_error := v4555_upper_checked
  lower_error := reuse_lower_error 77 90 Primitive.Addresses.material4555

def v4556_pa : Scalar.QComplex := ((999997227851447987075952659965 : Int)/10^30,(-2354631482677969645627324644 : Int)/10^30)
theorem v4556_pa_checked : Scalar.distance (sourceCoefficient 77 91 1 0) v4556_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4556_pb : Scalar.QComplex := ((-1015970541751155571858737 : Int)/10^30,(-431476319247379162218342701 : Int)/10^30)
theorem v4556_pb_checked : Scalar.distance (sourceCoefficient 77 91 1 1) v4556_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4556_pg : Scalar.QComplex := ((-93086171239883268848914 : Int)/10^30,(219184237014646981576 : Int)/10^30)
theorem v4556_pg_checked : Scalar.distance (sourceCoefficient 77 91 1 2) v4556_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4556_mb : Scalar.QComplex := ((-1388314793997345876292082 : Int)/10^30,(-431475281852206147819994481 : Int)/10^30)
theorem v4556_mb_checked : Scalar.distance (sourceCoefficient 77 91 3 1) v4556_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4556_mg : Scalar.QComplex := ((-93085947433522615990963 : Int)/10^30,(299513328736835836467 : Int)/10^30)
theorem v4556_mg_checked : Scalar.distance (sourceCoefficient 77 91 3 2) v4556_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4556_upper : Scalar.QComplex := ((999991674592716425698641018092 : Int)/10^30,(-4080532471962717432081116891 : Int)/10^30)
theorem v4556_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 77 91 5) 1) 14) v4556_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4556 : Material (77 : Basis) (91 : Basis) where
  plus := ![v4556_pa,v4556_pb,v4556_pg]
  minus := ![(Primitive.Addresses.material4556 1).one,v4556_mb,v4556_mg]
  upper := v4556_upper
  lower := (Primitive.Addresses.material4556 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4556_pa_checked.trans (by decide +kernel)
    · exact v4556_pb_checked.trans (by decide +kernel)
    · exact v4556_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 77 91 Primitive.Addresses.material4556
    · exact v4556_mb_checked.trans (by decide +kernel)
    · exact v4556_mg_checked.trans (by decide +kernel)
  upper_error := v4556_upper_checked
  lower_error := reuse_lower_error 77 91 Primitive.Addresses.material4556

def v4557_pa : Scalar.QComplex := ((999997152096003057257716344140 : Int)/10^30,(-2386587497521997152571227866 : Int)/10^30)
theorem v4557_pa_checked : Scalar.distance (sourceCoefficient 77 92 1 0) v4557_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4557_pb : Scalar.QComplex := ((-1029758840391718424821520 : Int)/10^30,(-431476285200773258658530891 : Int)/10^30)
theorem v4557_pb_checked : Scalar.distance (sourceCoefficient 77 92 1 1) v4557_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4557_pg : Scalar.QComplex := ((-93086164041394863525685 : Int)/10^30,(222158907980716679022 : Int)/10^30)
theorem v4557_pg_checked : Scalar.distance (sourceCoefficient 77 92 1 2) v4557_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4557_mb : Scalar.QComplex := ((-1402103058123207496430297 : Int)/10^30,(-431475235906932196479921368 : Int)/10^30)
theorem v4557_mb_checked : Scalar.distance (sourceCoefficient 77 92 3 1) v4557_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4557_mg : Scalar.QComplex := ((-93085937668029821482762 : Int)/10^30,(302487992383328298154 : Int)/10^30)
theorem v4557_mg_checked : Scalar.distance (sourceCoefficient 77 92 3 2) v4557_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4557_upper : Scalar.QComplex := ((999991543684201730945984872518 : Int)/10^30,(-4112488308464989177453791243 : Int)/10^30)
theorem v4557_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 77 92 5) 1) 14) v4557_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4557 : Material (77 : Basis) (92 : Basis) where
  plus := ![v4557_pa,v4557_pb,v4557_pg]
  minus := ![(Primitive.Addresses.material4557 1).one,v4557_mb,v4557_mg]
  upper := v4557_upper
  lower := (Primitive.Addresses.material4557 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4557_pa_checked.trans (by decide +kernel)
    · exact v4557_pb_checked.trans (by decide +kernel)
    · exact v4557_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 77 92 Primitive.Addresses.material4557
    · exact v4557_mb_checked.trans (by decide +kernel)
    · exact v4557_mg_checked.trans (by decide +kernel)
  upper_error := v4557_upper_checked
  lower_error := reuse_lower_error 77 92 Primitive.Addresses.material4557

def v4558_pa : Scalar.QComplex := ((999997060864038396696502647042 : Int)/10^30,(-2424512999488022172838063515 : Int)/10^30)
theorem v4558_pa_checked : Scalar.distance (sourceCoefficient 77 93 1 0) v4558_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4558_pb : Scalar.QComplex := ((-1046122837322580143818647 : Int)/10^30,(-431476244031784933482398036 : Int)/10^30)
theorem v4558_pb_checked : Scalar.distance (sourceCoefficient 77 93 1 1) v4558_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4558_pg : Scalar.QComplex := ((-93086155354292460400360 : Int)/10^30,(225689257060255201814 : Int)/10^30)
theorem v4558_pg_checked : Scalar.distance (sourceCoefficient 77 93 1 2) v4558_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4558_mb : Scalar.QComplex := ((-1418467013434022544238936 : Int)/10^30,(-431475180616566856128772018 : Int)/10^30)
theorem v4558_mb_checked : Scalar.distance (sourceCoefficient 77 93 3 1) v4558_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4558_mg : Scalar.QComplex := ((-93085925934398398341084 : Int)/10^30,(306018332651778392381 : Int)/10^30)
theorem v4558_mg_checked : Scalar.distance (sourceCoefficient 77 93 3 2) v4558_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4558_upper : Scalar.QComplex := ((999991386996397130982152171041 : Int)/10^30,(-4150413596487339556789836797 : Int)/10^30)
theorem v4558_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 77 93 5) 1) 14) v4558_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4558 : Material (77 : Basis) (93 : Basis) where
  plus := ![v4558_pa,v4558_pb,v4558_pg]
  minus := ![(Primitive.Addresses.material4558 1).one,v4558_mb,v4558_mg]
  upper := v4558_upper
  lower := (Primitive.Addresses.material4558 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4558_pa_checked.trans (by decide +kernel)
    · exact v4558_pb_checked.trans (by decide +kernel)
    · exact v4558_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 77 93 Primitive.Addresses.material4558
    · exact v4558_mb_checked.trans (by decide +kernel)
    · exact v4558_mg_checked.trans (by decide +kernel)
  upper_error := v4558_upper_checked
  lower_error := reuse_lower_error 77 93 Primitive.Addresses.material4558

def v4559_pa : Scalar.QComplex := ((999996951245900996216755604842 : Int)/10^30,(-2469311422867923780993805357 : Int)/10^30)
theorem v4559_pa_checked : Scalar.distance (sourceCoefficient 77 94 1 0) v4559_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4559_pb : Scalar.QComplex := ((-1065452343671835218895778 : Int)/10^30,(-431476194336068926264253850 : Int)/10^30)
theorem v4559_pb_checked : Scalar.distance (sourceCoefficient 77 94 1 1) v4559_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4559_pg : Scalar.QComplex := ((-93086144891665594037725 : Int)/10^30,(229859381676460563379 : Int)/10^30)
theorem v4559_pg_checked : Scalar.distance (sourceCoefficient 77 94 1 2) v4559_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4559_mb : Scalar.QComplex := ((-1437796469700854301140666 : Int)/10^30,(-431475114240375942138717073 : Int)/10^30)
theorem v4559_mb_checked : Scalar.distance (sourceCoefficient 77 94 3 1) v4559_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4559_mg : Scalar.QComplex := ((-93085911873145699348046 : Int)/10^30,(310188446686480008773 : Int)/10^30)
theorem v4559_mg_checked : Scalar.distance (sourceCoefficient 77 94 3 2) v4559_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4559_upper : Scalar.QComplex := ((999991200060408321353400895121 : Int)/10^30,(-4195211763954291259570161246 : Int)/10^30)
theorem v4559_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 77 94 5) 1) 14) v4559_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4559 : Material (77 : Basis) (94 : Basis) where
  plus := ![v4559_pa,v4559_pb,v4559_pg]
  minus := ![(Primitive.Addresses.material4559 1).one,v4559_mb,v4559_mg]
  upper := v4559_upper
  lower := (Primitive.Addresses.material4559 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4559_pa_checked.trans (by decide +kernel)
    · exact v4559_pb_checked.trans (by decide +kernel)
    · exact v4559_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 77 94 Primitive.Addresses.material4559
    · exact v4559_mb_checked.trans (by decide +kernel)
    · exact v4559_mg_checked.trans (by decide +kernel)
  upper_error := v4559_upper_checked
  lower_error := reuse_lower_error 77 94 Primitive.Addresses.material4559

def v4560_pa : Scalar.QComplex := ((999996840938954322435025654037 : Int)/10^30,(-2513585509126045155014016587 : Int)/10^30)
theorem v4560_pa_checked : Scalar.distance (sourceCoefficient 77 95 1 0) v4560_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4560_pb : Scalar.QComplex := ((-1084555609489593643882772 : Int)/10^30,(-431476144087617095166779775 : Int)/10^30)
theorem v4560_pb_checked : Scalar.distance (sourceCoefficient 77 95 1 1) v4560_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4560_pg : Scalar.QComplex := ((-93086134337356055864057 : Int)/10^30,(233980697530245563889 : Int)/10^30)
theorem v4560_pg_checked : Scalar.distance (sourceCoefficient 77 95 1 2) v4560_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4560_mb : Scalar.QComplex := ((-1456899685043442975821070 : Int)/10^30,(-431475047506684799264463010 : Int)/10^30)
theorem v4560_mb_checked : Scalar.distance (sourceCoefficient 77 95 3 1) v4560_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4560_mg : Scalar.QComplex := ((-93085897762330126385341 : Int)/10^30,(314309751897816980492 : Int)/10^30)
theorem v4560_mg_checked : Scalar.distance (sourceCoefficient 77 95 3 2) v4560_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4560_upper : Scalar.QComplex := ((999991013340569569023739144730 : Int)/10^30,(-4239485593891578960711539442 : Int)/10^30)
theorem v4560_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 77 95 5) 1) 14) v4560_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4560 : Material (77 : Basis) (95 : Basis) where
  plus := ![v4560_pa,v4560_pb,v4560_pg]
  minus := ![(Primitive.Addresses.material4560 1).one,v4560_mb,v4560_mg]
  upper := v4560_upper
  lower := (Primitive.Addresses.material4560 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4560_pa_checked.trans (by decide +kernel)
    · exact v4560_pb_checked.trans (by decide +kernel)
    · exact v4560_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 77 95 Primitive.Addresses.material4560
    · exact v4560_mb_checked.trans (by decide +kernel)
    · exact v4560_mg_checked.trans (by decide +kernel)
  upper_error := v4560_upper_checked
  lower_error := reuse_lower_error 77 95 Primitive.Addresses.material4560

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
