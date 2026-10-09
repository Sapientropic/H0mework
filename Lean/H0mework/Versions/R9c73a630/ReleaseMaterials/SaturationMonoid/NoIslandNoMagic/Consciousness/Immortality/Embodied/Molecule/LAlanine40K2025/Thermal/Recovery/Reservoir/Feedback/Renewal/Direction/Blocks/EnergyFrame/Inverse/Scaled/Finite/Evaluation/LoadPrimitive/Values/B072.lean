import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B048

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1153_pa : Scalar.QComplex := ((999999629105454688345695978350 : Int)/10^30,(-861271706873356467454742986 : Int)/10^30)
theorem v1153_pa_checked : Scalar.distance (sourceCoefficient 12 68 1 0) v1153_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1153_pb : Scalar.QComplex := ((-371619326260754009119814 : Int)/10^30,(-431477297423653527461055071 : Int)/10^30)
theorem v1153_pb_checked : Scalar.distance (sourceCoefficient 12 68 1 1) v1153_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1153_pg : Scalar.QComplex := ((-93086388517238008872155 : Int)/10^30,(80172702460536015260 : Int)/10^30)
theorem v1153_pg_checked : Scalar.distance (sourceCoefficient 12 68 1 2) v1153_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1153_mb : Scalar.QComplex := ((-743964662550419499174633 : Int)/10^30,(-431476816074194760093409934 : Int)/10^30)
theorem v1153_mb_checked : Scalar.distance (sourceCoefficient 12 68 3 1) v1153_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1153_mg : Scalar.QComplex := ((-93086284671489926819986 : Int)/10^30,(160502033443643657475 : Int)/10^30)
theorem v1153_mg_checked : Scalar.distance (sourceCoefficient 12 68 3 2) v1153_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1153_upper : Scalar.QComplex := ((999996653246643239382521878318 : Int)/10^30,(-2587179064688643457441839328 : Int)/10^30)
theorem v1153_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 68 5) 1) 14) v1153_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1153 : Material (12 : Basis) (68 : Basis) where
  plus := ![v1153_pa,v1153_pb,v1153_pg]
  minus := ![(Primitive.Addresses.material1153 1).one,v1153_mb,v1153_mg]
  upper := v1153_upper
  lower := (Primitive.Addresses.material1153 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1153_pa_checked.trans (by decide +kernel)
    · exact v1153_pb_checked.trans (by decide +kernel)
    · exact v1153_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 68 Primitive.Addresses.material1153
    · exact v1153_mb_checked.trans (by decide +kernel)
    · exact v1153_mg_checked.trans (by decide +kernel)
  upper_error := v1153_upper_checked
  lower_error := reuse_lower_error 12 68 Primitive.Addresses.material1153

def v1154_pa : Scalar.QComplex := ((999999610237462422561422742636 : Int)/10^30,(-882907086413990368369929019 : Int)/10^30)
theorem v1154_pa_checked : Scalar.distance (sourceCoefficient 12 69 1 0) v1154_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1154_pb : Scalar.QComplex := ((-380954502203761146408925 : Int)/10^30,(-431477286323807152242759467 : Int)/10^30)
theorem v1154_pb_checked : Scalar.distance (sourceCoefficient 12 69 1 1) v1154_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1154_pg : Scalar.QComplex := ((-93086386441727377456298 : Int)/10^30,(82186662271354336953 : Int)/10^30)
theorem v1154_pg_checked : Scalar.distance (sourceCoefficient 12 69 1 2) v1154_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1154_mb : Scalar.QComplex := ((-753299825438846490974718 : Int)/10^30,(-431476796918516119757028374 : Int)/10^30)
theorem v1154_mb_checked : Scalar.distance (sourceCoefficient 12 69 3 1) v1154_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1154_mg : Scalar.QComplex := ((-93086280858023456858117 : Int)/10^30,(162515990713500501707 : Int)/10^30)
theorem v1154_mg_checked : Scalar.distance (sourceCoefficient 12 69 3 2) v1154_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1154_upper : Scalar.QComplex := ((999996597037976734422019100497 : Int)/10^30,(-2608814379441478042935918715 : Int)/10^30)
theorem v1154_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 69 5) 1) 14) v1154_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1154 : Material (12 : Basis) (69 : Basis) where
  plus := ![v1154_pa,v1154_pb,v1154_pg]
  minus := ![(Primitive.Addresses.material1154 1).one,v1154_mb,v1154_mg]
  upper := v1154_upper
  lower := (Primitive.Addresses.material1154 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1154_pa_checked.trans (by decide +kernel)
    · exact v1154_pb_checked.trans (by decide +kernel)
    · exact v1154_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 69 Primitive.Addresses.material1154
    · exact v1154_mb_checked.trans (by decide +kernel)
    · exact v1154_mg_checked.trans (by decide +kernel)
  upper_error := v1154_upper_checked
  lower_error := reuse_lower_error 12 69 Primitive.Addresses.material1154

def v1155_pa : Scalar.QComplex := ((999999597570684251766541509697 : Int)/10^30,(-897139046941505463414415106 : Int)/10^30)
theorem v1155_pa_checked : Scalar.distance (sourceCoefficient 12 70 1 0) v1155_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1155_pb : Scalar.QComplex := ((-387095270525662867472342 : Int)/10^30,(-431477278875386062565991898 : Int)/10^30)
theorem v1155_pb_checked : Scalar.distance (sourceCoefficient 12 70 1 1) v1155_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1155_pg : Scalar.QComplex := ((-93086385048718189466140 : Int)/10^30,(83511464373298504993 : Int)/10^30)
theorem v1155_pg_checked : Scalar.distance (sourceCoefficient 12 70 1 2) v1155_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1155_mb : Scalar.QComplex := ((-759440585046607582859376 : Int)/10^30,(-431476784170891311605116619 : Int)/10^30)
theorem v1155_mb_checked : Scalar.distance (sourceCoefficient 12 70 3 1) v1155_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1155_mg : Scalar.QComplex := ((-93086278321770240442859 : Int)/10^30,(163840791120056110316 : Int)/10^30)
theorem v1155_mg_checked : Scalar.distance (sourceCoefficient 12 70 3 2) v1155_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1155_upper : Scalar.QComplex := ((999996559808144672187656912425 : Int)/10^30,(-2623046296910449734115272576 : Int)/10^30)
theorem v1155_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 70 5) 1) 14) v1155_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1155 : Material (12 : Basis) (70 : Basis) where
  plus := ![v1155_pa,v1155_pb,v1155_pg]
  minus := ![(Primitive.Addresses.material1155 1).one,v1155_mb,v1155_mg]
  upper := v1155_upper
  lower := (Primitive.Addresses.material1155 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1155_pa_checked.trans (by decide +kernel)
    · exact v1155_pb_checked.trans (by decide +kernel)
    · exact v1155_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 70 Primitive.Addresses.material1155
    · exact v1155_mb_checked.trans (by decide +kernel)
    · exact v1155_mg_checked.trans (by decide +kernel)
  upper_error := v1155_upper_checked
  lower_error := reuse_lower_error 12 70 Primitive.Addresses.material1155

def v1156_pa : Scalar.QComplex := ((999999575481579656781146620501 : Int)/10^30,(-921431853405637641274707549 : Int)/10^30)
theorem v1156_pa_checked : Scalar.distance (sourceCoefficient 12 71 1 0) v1156_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1156_pb : Scalar.QComplex := ((-397577065592351939008655 : Int)/10^30,(-431477265892327111303886849 : Int)/10^30)
theorem v1156_pb_checked : Scalar.distance (sourceCoefficient 12 71 1 1) v1156_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1156_pg : Scalar.QComplex := ((-93086382620145649622859 : Int)/10^30,(85772794476638361389 : Int)/10^30)
theorem v1156_pg_checked : Scalar.distance (sourceCoefficient 12 71 1 2) v1156_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1156_mb : Scalar.QComplex := ((-769922365006650169697234 : Int)/10^30,(-431476762142520134501822086 : Int)/10^30)
theorem v1156_mb_checked : Scalar.distance (sourceCoefficient 12 71 3 1) v1156_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1156_mg : Scalar.QComplex := ((-93086273941772572212964 : Int)/10^30,(166102118285650698309 : Int)/10^30)
theorem v1156_mg_checked : Scalar.distance (sourceCoefficient 12 71 3 2) v1156_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1156_upper : Scalar.QComplex := ((999996495791892845423729417000 : Int)/10^30,(-2647339029069509694125179423 : Int)/10^30)
theorem v1156_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 71 5) 1) 14) v1156_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1156 : Material (12 : Basis) (71 : Basis) where
  plus := ![v1156_pa,v1156_pb,v1156_pg]
  minus := ![(Primitive.Addresses.material1156 1).one,v1156_mb,v1156_mg]
  upper := v1156_upper
  lower := (Primitive.Addresses.material1156 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1156_pa_checked.trans (by decide +kernel)
    · exact v1156_pb_checked.trans (by decide +kernel)
    · exact v1156_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 71 Primitive.Addresses.material1156
    · exact v1156_mb_checked.trans (by decide +kernel)
    · exact v1156_mg_checked.trans (by decide +kernel)
  upper_error := v1156_upper_checked
  lower_error := reuse_lower_error 12 71 Primitive.Addresses.material1156

def v1157_pa : Scalar.QComplex := ((999999550842722283147205835569 : Int)/10^30,(-947794468063327252038161881 : Int)/10^30)
theorem v1157_pa_checked : Scalar.distance (sourceCoefficient 12 72 1 0) v1157_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1157_pb : Scalar.QComplex := ((-408951935673784492260825 : Int)/10^30,(-431477251418945905196973220 : Int)/10^30)
theorem v1157_pb_checked : Scalar.distance (sourceCoefficient 12 72 1 1) v1157_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1157_pg : Scalar.QComplex := ((-93086379912139270973395 : Int)/10^30,(88226795560474147340 : Int)/10^30)
theorem v1157_pg_checked : Scalar.distance (sourceCoefficient 12 72 1 2) v1157_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1157_mb : Scalar.QComplex := ((-781297218362822610409066 : Int)/10^30,(-431476737853143742350711565 : Int)/10^30)
theorem v1157_mb_checked : Scalar.distance (sourceCoefficient 12 72 3 1) v1157_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1157_mg : Scalar.QComplex := ((-93086269116074790633722 : Int)/10^30,(168556116118862186663 : Int)/10^30)
theorem v1157_mg_checked : Scalar.distance (sourceCoefficient 12 72 3 2) v1157_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1157_upper : Scalar.QComplex := ((999996425653590867020904444142 : Int)/10^30,(-2673701561938748935302072675 : Int)/10^30)
theorem v1157_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 72 5) 1) 14) v1157_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1157 : Material (12 : Basis) (72 : Basis) where
  plus := ![v1157_pa,v1157_pb,v1157_pg]
  minus := ![(Primitive.Addresses.material1157 1).one,v1157_mb,v1157_mg]
  upper := v1157_upper
  lower := (Primitive.Addresses.material1157 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1157_pa_checked.trans (by decide +kernel)
    · exact v1157_pb_checked.trans (by decide +kernel)
    · exact v1157_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 72 Primitive.Addresses.material1157
    · exact v1157_mb_checked.trans (by decide +kernel)
    · exact v1157_mg_checked.trans (by decide +kernel)
  upper_error := v1157_upper_checked
  lower_error := reuse_lower_error 12 72 Primitive.Addresses.material1157

def v1158_pa : Scalar.QComplex := ((999999541841755420309931571283 : Int)/10^30,(-957244106406721660372859386 : Int)/10^30)
theorem v1158_pa_checked : Scalar.distance (sourceCoefficient 12 73 1 0) v1158_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1158_pb : Scalar.QComplex := ((-413029240142780723320683 : Int)/10^30,(-431477246133639769269497109 : Int)/10^30)
theorem v1158_pb_checked : Scalar.distance (sourceCoefficient 12 73 1 1) v1158_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1158_pg : Scalar.QComplex := ((-93086378923082607729502 : Int)/10^30,(89106428435708533064 : Int)/10^30)
theorem v1158_pg_checked : Scalar.distance (sourceCoefficient 12 73 1 2) v1158_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1158_mb : Scalar.QComplex := ((-785374516752670891688351 : Int)/10^30,(-431476729049309452616945715 : Int)/10^30)
theorem v1158_mb_checked : Scalar.distance (sourceCoefficient 12 73 3 1) v1158_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1158_mg : Scalar.QComplex := ((-93086267367934941527593 : Int)/10^30,(169435747813057696808 : Int)/10^30)
theorem v1158_mg_checked : Scalar.distance (sourceCoefficient 12 73 3 2) v1158_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1158_upper : Scalar.QComplex := ((999996400343418893861625761179 : Int)/10^30,(-2683151170673164819724178086 : Int)/10^30)
theorem v1158_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 73 5) 1) 14) v1158_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1158 : Material (12 : Basis) (73 : Basis) where
  plus := ![v1158_pa,v1158_pb,v1158_pg]
  minus := ![(Primitive.Addresses.material1158 1).one,v1158_mb,v1158_mg]
  upper := v1158_upper
  lower := (Primitive.Addresses.material1158 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1158_pa_checked.trans (by decide +kernel)
    · exact v1158_pb_checked.trans (by decide +kernel)
    · exact v1158_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 73 Primitive.Addresses.material1158
    · exact v1158_mb_checked.trans (by decide +kernel)
    · exact v1158_mg_checked.trans (by decide +kernel)
  upper_error := v1158_upper_checked
  lower_error := reuse_lower_error 12 73 Primitive.Addresses.material1158

def v1159_pa : Scalar.QComplex := ((999999531606683263253173314353 : Int)/10^30,(-967877272220602610488921902 : Int)/10^30)
theorem v1159_pa_checked : Scalar.distance (sourceCoefficient 12 74 1 0) v1159_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1159_pb : Scalar.QComplex := ((-417617209806515730363089 : Int)/10^30,(-431477240124944991171561675 : Int)/10^30)
theorem v1159_pb_checked : Scalar.distance (sourceCoefficient 12 74 1 1) v1159_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1159_pg : Scalar.QComplex := ((-93086377798555227707385 : Int)/10^30,(90096231625034853610 : Int)/10^30)
theorem v1159_pg_checked : Scalar.distance (sourceCoefficient 12 74 1 2) v1159_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1159_mb : Scalar.QComplex := ((-789962479522862140418493 : Int)/10^30,(-431476719081405726510398061 : Int)/10^30)
theorem v1159_mb_checked : Scalar.distance (sourceCoefficient 12 74 3 1) v1159_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1159_mg : Scalar.QComplex := ((-93086265389252406910592 : Int)/10^30,(170425549663418571602 : Int)/10^30)
theorem v1159_mg_checked : Scalar.distance (sourceCoefficient 12 74 3 2) v1159_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1159_upper : Scalar.QComplex := ((999996371756482419251363228319 : Int)/10^30,(-2693784302985388324875636034 : Int)/10^30)
theorem v1159_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 74 5) 1) 14) v1159_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1159 : Material (12 : Basis) (74 : Basis) where
  plus := ![v1159_pa,v1159_pb,v1159_pg]
  minus := ![(Primitive.Addresses.material1159 1).one,v1159_mb,v1159_mg]
  upper := v1159_upper
  lower := (Primitive.Addresses.material1159 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1159_pa_checked.trans (by decide +kernel)
    · exact v1159_pb_checked.trans (by decide +kernel)
    · exact v1159_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 74 Primitive.Addresses.material1159
    · exact v1159_mb_checked.trans (by decide +kernel)
    · exact v1159_mg_checked.trans (by decide +kernel)
  upper_error := v1159_upper_checked
  lower_error := reuse_lower_error 12 74 Primitive.Addresses.material1159

def v1160_pa : Scalar.QComplex := ((999999517157712705127708182236 : Int)/10^30,(-982692394115813935707597987 : Int)/10^30)
theorem v1160_pa_checked : Scalar.distance (sourceCoefficient 12 75 1 0) v1160_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1160_pb : Scalar.QComplex := ((-424009598501078297301003 : Int)/10^30,(-431477231644618637085860314 : Int)/10^30)
theorem v1160_pb_checked : Scalar.distance (sourceCoefficient 12 75 1 1) v1160_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1160_pg : Scalar.QComplex := ((-93086376211286087808593 : Int)/10^30,(91475318066785881430 : Int)/10^30)
theorem v1160_pg_checked : Scalar.distance (sourceCoefficient 12 75 1 2) v1160_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1160_mb : Scalar.QComplex := ((-796354858519106545919846 : Int)/10^30,(-431476705084738989129633073 : Int)/10^30)
theorem v1160_mb_checked : Scalar.distance (sourceCoefficient 12 75 3 1) v1160_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1160_mg : Scalar.QComplex := ((-93086262611894370541146 : Int)/10^30,(171804634221930910010 : Int)/10^30)
theorem v1160_mg_checked : Scalar.distance (sourceCoefficient 12 75 3 2) v1160_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1160_upper : Scalar.QComplex := ((999996331737977007394947907880 : Int)/10^30,(-2708599377877603510689786152 : Int)/10^30)
theorem v1160_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 75 5) 1) 14) v1160_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1160 : Material (12 : Basis) (75 : Basis) where
  plus := ![v1160_pa,v1160_pb,v1160_pg]
  minus := ![(Primitive.Addresses.material1160 1).one,v1160_mb,v1160_mg]
  upper := v1160_upper
  lower := (Primitive.Addresses.material1160 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1160_pa_checked.trans (by decide +kernel)
    · exact v1160_pb_checked.trans (by decide +kernel)
    · exact v1160_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 75 Primitive.Addresses.material1160
    · exact v1160_mb_checked.trans (by decide +kernel)
    · exact v1160_mg_checked.trans (by decide +kernel)
  upper_error := v1160_upper_checked
  lower_error := reuse_lower_error 12 75 Primitive.Addresses.material1160

def v1161_pa : Scalar.QComplex := ((999999504865409767810209112667 : Int)/10^30,(-995122573006017755350493680 : Int)/10^30)
theorem v1161_pa_checked : Scalar.distance (sourceCoefficient 12 76 1 0) v1161_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1161_pb : Scalar.QComplex := ((-429372938367701096726008 : Int)/10^30,(-431477224432040571214237303 : Int)/10^30)
theorem v1161_pb_checked : Scalar.distance (sourceCoefficient 12 76 1 1) v1161_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1161_pg : Scalar.QComplex := ((-93086374861146421895426 : Int)/10^30,(92632398729131503090 : Int)/10^30)
theorem v1161_pg_checked : Scalar.distance (sourceCoefficient 12 76 1 2) v1161_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1161_mb : Scalar.QComplex := ((-801718190164582767870423 : Int)/10^30,(-431476693243842859795596832 : Int)/10^30)
theorem v1161_mb_checked : Scalar.distance (sourceCoefficient 12 76 3 1) v1161_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1161_mg : Scalar.QComplex := ((-93086260263246708720917 : Int)/10^30,(172961713288332796230 : Int)/10^30)
theorem v1161_mg_checked : Scalar.distance (sourceCoefficient 12 76 3 2) v1161_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1161_upper : Scalar.QComplex := ((999996297992331270547071994182 : Int)/10^30,(-2721029517039116303957980146 : Int)/10^30)
theorem v1161_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 76 5) 1) 14) v1161_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1161 : Material (12 : Basis) (76 : Basis) where
  plus := ![v1161_pa,v1161_pb,v1161_pg]
  minus := ![(Primitive.Addresses.material1161 1).one,v1161_mb,v1161_mg]
  upper := v1161_upper
  lower := (Primitive.Addresses.material1161 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1161_pa_checked.trans (by decide +kernel)
    · exact v1161_pb_checked.trans (by decide +kernel)
    · exact v1161_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 76 Primitive.Addresses.material1161
    · exact v1161_mb_checked.trans (by decide +kernel)
    · exact v1161_mg_checked.trans (by decide +kernel)
  upper_error := v1161_upper_checked
  lower_error := reuse_lower_error 12 76 Primitive.Addresses.material1161

def v1162_pa : Scalar.QComplex := ((999999501997611517771548051926 : Int)/10^30,(-998000265009021913882799023 : Int)/10^30)
theorem v1162_pa_checked : Scalar.distance (sourceCoefficient 12 77 1 0) v1162_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1162_pb : Scalar.QComplex := ((-430614597096551486352992 : Int)/10^30,(-431477222749596030028947988 : Int)/10^30)
theorem v1162_pb_checked : Scalar.distance (sourceCoefficient 12 77 1 1) v1162_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1162_pg : Scalar.QComplex := ((-93086374546185611701726 : Int)/10^30,(92900272730380022852 : Int)/10^30)
theorem v1162_pg_checked : Scalar.distance (sourceCoefficient 12 77 1 2) v1162_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1162_mb : Scalar.QComplex := ((-802959846979233001585508 : Int)/10^30,(-431476690489903384296632011 : Int)/10^30)
theorem v1162_mb_checked : Scalar.distance (sourceCoefficient 12 77 3 1) v1162_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1162_mg : Scalar.QComplex := ((-93086259717122817321205 : Int)/10^30,(173229586918042588991 : Int)/10^30)
theorem v1162_mg_checked : Scalar.distance (sourceCoefficient 12 77 3 2) v1162_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1162_upper : Scalar.QComplex := ((999996290157901956751058199745 : Int)/10^30,(-2723907199806576646522319844 : Int)/10^30)
theorem v1162_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 77 5) 1) 14) v1162_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1162 : Material (12 : Basis) (77 : Basis) where
  plus := ![v1162_pa,v1162_pb,v1162_pg]
  minus := ![(Primitive.Addresses.material1162 1).one,v1162_mb,v1162_mg]
  upper := v1162_upper
  lower := (Primitive.Addresses.material1162 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1162_pa_checked.trans (by decide +kernel)
    · exact v1162_pb_checked.trans (by decide +kernel)
    · exact v1162_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 77 Primitive.Addresses.material1162
    · exact v1162_mb_checked.trans (by decide +kernel)
    · exact v1162_mg_checked.trans (by decide +kernel)
  upper_error := v1162_upper_checked
  lower_error := reuse_lower_error 12 77 Primitive.Addresses.material1162

def v1163_pa : Scalar.QComplex := ((999999484582979040065238387010 : Int)/10^30,(-1015299845496474025742447103 : Int)/10^30)
theorem v1163_pa_checked : Scalar.distance (sourceCoefficient 12 78 1 0) v1163_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1163_pb : Scalar.QComplex := ((-438078973015371167838561 : Int)/10^30,(-431477212534977509373041902 : Int)/10^30)
theorem v1163_pb_checked : Scalar.distance (sourceCoefficient 12 78 1 1) v1163_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1163_pg : Scalar.QComplex := ((-93086372633807999715909 : Int)/10^30,(94510628465319042681 : Int)/10^30)
theorem v1163_pg_checked : Scalar.distance (sourceCoefficient 12 78 1 2) v1163_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1163_mb : Scalar.QComplex := ((-810424211303968655676709 : Int)/10^30,(-431476673833868432080330803 : Int)/10^30)
theorem v1163_mb_checked : Scalar.distance (sourceCoefficient 12 78 3 1) v1163_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1163_mg : Scalar.QComplex := ((-93086256415081445878545 : Int)/10^30,(174839940403076822956 : Int)/10^30)
theorem v1163_mg_checked : Scalar.distance (sourceCoefficient 12 78 3 2) v1163_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1163_upper : Scalar.QComplex := ((999996242885788900434109826022 : Int)/10^30,(-2741206724472259960393188563 : Int)/10^30)
theorem v1163_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 78 5) 1) 14) v1163_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1163 : Material (12 : Basis) (78 : Basis) where
  plus := ![v1163_pa,v1163_pb,v1163_pg]
  minus := ![(Primitive.Addresses.material1163 1).one,v1163_mb,v1163_mg]
  upper := v1163_upper
  lower := (Primitive.Addresses.material1163 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1163_pa_checked.trans (by decide +kernel)
    · exact v1163_pb_checked.trans (by decide +kernel)
    · exact v1163_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 78 Primitive.Addresses.material1163
    · exact v1163_mb_checked.trans (by decide +kernel)
    · exact v1163_mg_checked.trans (by decide +kernel)
  upper_error := v1163_upper_checked
  lower_error := reuse_lower_error 12 78 Primitive.Addresses.material1163

def v1164_pa : Scalar.QComplex := ((999999478905017582879905467549 : Int)/10^30,(-1020876923676042100772009132 : Int)/10^30)
theorem v1164_pa_checked : Scalar.distance (sourceCoefficient 12 79 1 0) v1164_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1164_pb : Scalar.QComplex := ((-440485355504504029650131 : Int)/10^30,(-431477209205265470659814173 : Int)/10^30)
theorem v1164_pb_checked : Scalar.distance (sourceCoefficient 12 79 1 1) v1164_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1164_pg : Scalar.QComplex := ((-93086372010363425477925 : Int)/10^30,(95029778613644260181 : Int)/10^30)
theorem v1164_pg_checked : Scalar.distance (sourceCoefficient 12 79 1 2) v1164_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1164_mb : Scalar.QComplex := ((-812830590023703814925139 : Int)/10^30,(-431476668427557924493487167 : Int)/10^30)
theorem v1164_mb_checked : Scalar.distance (sourceCoefficient 12 79 3 1) v1164_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1164_mg : Scalar.QComplex := ((-93086255343633907427519 : Int)/10^30,(175359089820094125234 : Int)/10^30)
theorem v1164_mg_checked : Scalar.distance (sourceCoefficient 12 79 3 2) v1164_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1164_upper : Scalar.QComplex := ((999996227582304910551086678102 : Int)/10^30,(-2746783784545778842117186775 : Int)/10^30)
theorem v1164_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 79 5) 1) 14) v1164_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1164 : Material (12 : Basis) (79 : Basis) where
  plus := ![v1164_pa,v1164_pb,v1164_pg]
  minus := ![(Primitive.Addresses.material1164 1).one,v1164_mb,v1164_mg]
  upper := v1164_upper
  lower := (Primitive.Addresses.material1164 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1164_pa_checked.trans (by decide +kernel)
    · exact v1164_pb_checked.trans (by decide +kernel)
    · exact v1164_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 79 Primitive.Addresses.material1164
    · exact v1164_mb_checked.trans (by decide +kernel)
    · exact v1164_mg_checked.trans (by decide +kernel)
  upper_error := v1164_upper_checked
  lower_error := reuse_lower_error 12 79 Primitive.Addresses.material1164

def v1165_pa : Scalar.QComplex := ((999999469973237916841472842073 : Int)/10^30,(-1029588870976152563209937329 : Int)/10^30)
theorem v1165_pa_checked : Scalar.distance (sourceCoefficient 12 80 1 0) v1165_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1165_pb : Scalar.QComplex := ((-444244362746882634440176 : Int)/10^30,(-431477203968117774421654101 : Int)/10^30)
theorem v1165_pb_checked : Scalar.distance (sourceCoefficient 12 80 1 1) v1165_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1165_pg : Scalar.QComplex := ((-93086371029721777370608 : Int)/10^30,(95840742449916877233 : Int)/10^30)
theorem v1165_pg_checked : Scalar.distance (sourceCoefficient 12 80 1 2) v1165_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1165_mb : Scalar.QComplex := ((-816589591347009638782514 : Int)/10^30,(-431476659946558227513535479 : Int)/10^30)
theorem v1165_mb_checked : Scalar.distance (sourceCoefficient 12 80 3 1) v1165_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1165_mg : Scalar.QComplex := ((-93086253663167358209971 : Int)/10^30,(176170052508158267308 : Int)/10^30)
theorem v1165_mg_checked : Scalar.distance (sourceCoefficient 12 80 3 2) v1165_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1165_upper : Scalar.QComplex := ((999996203614507849043863491837 : Int)/10^30,(-2755495703455025759398152236 : Int)/10^30)
theorem v1165_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 80 5) 1) 14) v1165_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1165 : Material (12 : Basis) (80 : Basis) where
  plus := ![v1165_pa,v1165_pb,v1165_pg]
  minus := ![(Primitive.Addresses.material1165 1).one,v1165_mb,v1165_mg]
  upper := v1165_upper
  lower := (Primitive.Addresses.material1165 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1165_pa_checked.trans (by decide +kernel)
    · exact v1165_pb_checked.trans (by decide +kernel)
    · exact v1165_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 80 Primitive.Addresses.material1165
    · exact v1165_mb_checked.trans (by decide +kernel)
    · exact v1165_mg_checked.trans (by decide +kernel)
  upper_error := v1165_upper_checked
  lower_error := reuse_lower_error 12 80 Primitive.Addresses.material1165

def v1166_pa : Scalar.QComplex := ((999999442620856709371626634637 : Int)/10^30,(-1055820996149322355071632048 : Int)/10^30)
theorem v1166_pa_checked : Scalar.distance (sourceCoefficient 12 81 1 0) v1166_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1166_pb : Scalar.QComplex := ((-455562928302637463593774 : Int)/10^30,(-431477187935116211155162452 : Int)/10^30)
theorem v1166_pb_checked : Scalar.distance (sourceCoefficient 12 81 1 1) v1166_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1166_pg : Scalar.QComplex := ((-93086368027183981916560 : Int)/10^30,(98282596599053315320 : Int)/10^30)
theorem v1166_pg_checked : Scalar.distance (sourceCoefficient 12 81 1 2) v1166_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1166_mb : Scalar.QComplex := ((-827908138852586978014173 : Int)/10^30,(-431476634146150328718959065 : Int)/10^30)
theorem v1166_mb_checked : Scalar.distance (sourceCoefficient 12 81 3 1) v1166_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1166_mg : Scalar.QComplex := ((-93086248553420527061559 : Int)/10^30,(178611903157025919229 : Int)/10^30)
theorem v1166_mg_checked : Scalar.distance (sourceCoefficient 12 81 3 2) v1166_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1166_upper : Scalar.QComplex := ((999996130987899090647775186830 : Int)/10^30,(-2781727742350797972252411507 : Int)/10^30)
theorem v1166_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 81 5) 1) 14) v1166_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1166 : Material (12 : Basis) (81 : Basis) where
  plus := ![v1166_pa,v1166_pb,v1166_pg]
  minus := ![(Primitive.Addresses.material1166 1).one,v1166_mb,v1166_mg]
  upper := v1166_upper
  lower := (Primitive.Addresses.material1166 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1166_pa_checked.trans (by decide +kernel)
    · exact v1166_pb_checked.trans (by decide +kernel)
    · exact v1166_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 81 Primitive.Addresses.material1166
    · exact v1166_mb_checked.trans (by decide +kernel)
    · exact v1166_mg_checked.trans (by decide +kernel)
  upper_error := v1166_upper_checked
  lower_error := reuse_lower_error 12 81 Primitive.Addresses.material1166

def v1167_pa : Scalar.QComplex := ((999999432076318305391256462453 : Int)/10^30,(-1065761249460642220396414732 : Int)/10^30)
theorem v1167_pa_checked : Scalar.distance (sourceCoefficient 12 82 1 0) v1167_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1167_pb : Scalar.QComplex := ((-459851921503075057112900 : Int)/10^30,(-431477181756232305732592286 : Int)/10^30)
theorem v1167_pb_checked : Scalar.distance (sourceCoefficient 12 82 1 1) v1167_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1167_pg : Scalar.QComplex := ((-93086366869894849939295 : Int)/10^30,(99207899005526122899 : Int)/10^30)
theorem v1167_pg_checked : Scalar.distance (sourceCoefficient 12 82 1 2) v1167_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1167_mb : Scalar.QComplex := ((-832197125123937862558642 : Int)/10^30,(-431476624266060761082586909 : Int)/10^30)
theorem v1167_mb_checked : Scalar.distance (sourceCoefficient 12 82 3 1) v1167_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1167_mg : Scalar.QComplex := ((-93086246597637523283268 : Int)/10^30,(179537204220277953941 : Int)/10^30)
theorem v1167_mg_checked : Scalar.distance (sourceCoefficient 12 82 3 2) v1167_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1167_upper : Scalar.QComplex := ((999996103287400948916762602807 : Int)/10^30,(-2791667962658361502325532553 : Int)/10^30)
theorem v1167_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 82 5) 1) 14) v1167_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1167 : Material (12 : Basis) (82 : Basis) where
  plus := ![v1167_pa,v1167_pb,v1167_pg]
  minus := ![(Primitive.Addresses.material1167 1).one,v1167_mb,v1167_mg]
  upper := v1167_upper
  lower := (Primitive.Addresses.material1167 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1167_pa_checked.trans (by decide +kernel)
    · exact v1167_pb_checked.trans (by decide +kernel)
    · exact v1167_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 82 Primitive.Addresses.material1167
    · exact v1167_mb_checked.trans (by decide +kernel)
    · exact v1167_mg_checked.trans (by decide +kernel)
  upper_error := v1167_upper_checked
  lower_error := reuse_lower_error 12 82 Primitive.Addresses.material1167

def v1168_pa : Scalar.QComplex := ((999999417523354345409279640402 : Int)/10^30,(-1079329862474924163392601279 : Int)/10^30)
theorem v1168_pa_checked : Scalar.distance (sourceCoefficient 12 83 1 0) v1168_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1168_pb : Scalar.QComplex := ((-465706469306758390060514 : Int)/10^30,(-431477173230195824136220181 : Int)/10^30)
theorem v1168_pb_checked : Scalar.distance (sourceCoefficient 12 83 1 1) v1168_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1168_pg : Scalar.QComplex := ((-93086365272854797694230 : Int)/10^30,(100470952350224235973 : Int)/10^30)
theorem v1168_pg_checked : Scalar.distance (sourceCoefficient 12 83 1 2) v1168_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1168_mb : Scalar.QComplex := ((-838051663390119996953062 : Int)/10^30,(-431476610687816378585391338 : Int)/10^30)
theorem v1168_mb_checked : Scalar.distance (sourceCoefficient 12 83 3 1) v1168_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1168_mg : Scalar.QComplex := ((-93086243910639915025677 : Int)/10^30,(180800255716509945320 : Int)/10^30)
theorem v1168_mg_checked : Scalar.distance (sourceCoefficient 12 83 3 2) v1168_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1168_upper : Scalar.QComplex := ((999996065316263536171578787148 : Int)/10^30,(-2805236530346692681445924619 : Int)/10^30)
theorem v1168_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 83 5) 1) 14) v1168_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1168 : Material (12 : Basis) (83 : Basis) where
  plus := ![v1168_pa,v1168_pb,v1168_pg]
  minus := ![(Primitive.Addresses.material1168 1).one,v1168_mb,v1168_mg]
  upper := v1168_upper
  lower := (Primitive.Addresses.material1168 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1168_pa_checked.trans (by decide +kernel)
    · exact v1168_pb_checked.trans (by decide +kernel)
    · exact v1168_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 83 Primitive.Addresses.material1168
    · exact v1168_mb_checked.trans (by decide +kernel)
    · exact v1168_mg_checked.trans (by decide +kernel)
  upper_error := v1168_upper_checked
  lower_error := reuse_lower_error 12 83 Primitive.Addresses.material1168

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
