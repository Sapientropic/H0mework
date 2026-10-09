import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B173
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B174

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4161_pa : Scalar.QComplex := ((999998744739019219839665365609 : Int)/10^30,(-1584462175591513071225206233 : Int)/10^30)
theorem v4161_pa_checked : Scalar.distance (sourceCoefficient 63 67 1 0) v4161_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4161_pb : Scalar.QComplex := ((-683659810043273988539878 : Int)/10^30,(-431476978373791751135244814 : Int)/10^30)
theorem v4161_pb_checked : Scalar.distance (sourceCoefficient 63 67 1 1) v4161_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4161_pg : Scalar.QComplex := ((-93086312940268487232681 : Int)/10^30,(147491927059991241701 : Int)/10^30)
theorem v4161_pg_checked : Scalar.distance (sourceCoefficient 63 67 1 2) v4161_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4161_mb : Scalar.QComplex := ((-1056004754820345171133539 : Int)/10^30,(-431476227747568057986361430 : Int)/10^30)
theorem v4161_mb_checked : Scalar.distance (sourceCoefficient 63 67 3 1) v4161_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4161_mg : Scalar.QComplex := ((-93086151001089661935300 : Int)/10^30,(227821167757554088162 : Int)/10^30)
theorem v4161_mg_checked : Scalar.distance (sourceCoefficient 63 67 3 2) v4161_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4161_upper : Scalar.QComplex := ((999994520720383250084643442665 : Int)/10^30,(-3310366929963310303189564019 : Int)/10^30)
theorem v4161_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 63 67 5) 1) 14) v4161_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4161 : Material (63 : Basis) (67 : Basis) where
  plus := ![v4161_pa,v4161_pb,v4161_pg]
  minus := ![(Primitive.Addresses.material4161 1).one,v4161_mb,v4161_mg]
  upper := v4161_upper
  lower := (Primitive.Addresses.material4161 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4161_pa_checked.trans (by decide +kernel)
    · exact v4161_pb_checked.trans (by decide +kernel)
    · exact v4161_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 63 67 Primitive.Addresses.material4161
    · exact v4161_mb_checked.trans (by decide +kernel)
    · exact v4161_mg_checked.trans (by decide +kernel)
  upper_error := v4161_upper_checked
  lower_error := reuse_lower_error 63 67 Primitive.Addresses.material4161

def v4162_pa : Scalar.QComplex := ((999998665641802321843335362836 : Int)/10^30,(-1633620095017355501915336592 : Int)/10^30)
theorem v4162_pa_checked : Scalar.distance (sourceCoefficient 63 68 1 0) v4162_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4162_pb : Scalar.QComplex := ((-704870345552376422008599 : Int)/10^30,(-431476943233465816937929155 : Int)/10^30)
theorem v4162_pb_checked : Scalar.distance (sourceCoefficient 63 68 1 1) v4162_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4162_pg : Scalar.QComplex := ((-93086305468264363525507 : Int)/10^30,(152067862096879000942 : Int)/10^30)
theorem v4162_pg_checked : Scalar.distance (sourceCoefficient 63 68 1 2) v4162_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4162_mb : Scalar.QComplex := ((-1077215252107277245519475 : Int)/10^30,(-431476174303518350840390722 : Int)/10^30)
theorem v4162_mb_checked : Scalar.distance (sourceCoefficient 63 68 3 1) v4162_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4162_mg : Scalar.QComplex := ((-93086139580262476026163 : Int)/10^30,(232397094642609070421 : Int)/10^30)
theorem v4162_mg_checked : Scalar.distance (sourceCoefficient 63 68 3 2) v4162_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4162_upper : Scalar.QComplex := ((999994356781174800711486585687 : Int)/10^30,(-3359524639659585521461562669 : Int)/10^30)
theorem v4162_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 63 68 5) 1) 14) v4162_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4162 : Material (63 : Basis) (68 : Basis) where
  plus := ![v4162_pa,v4162_pb,v4162_pg]
  minus := ![(Primitive.Addresses.material4162 1).one,v4162_mb,v4162_mg]
  upper := v4162_upper
  lower := (Primitive.Addresses.material4162 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4162_pa_checked.trans (by decide +kernel)
    · exact v4162_pb_checked.trans (by decide +kernel)
    · exact v4162_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 63 68 Primitive.Addresses.material4162
    · exact v4162_mb_checked.trans (by decide +kernel)
    · exact v4162_mg_checked.trans (by decide +kernel)
  upper_error := v4162_upper_checked
  lower_error := reuse_lower_error 63 68 Primitive.Addresses.material4162

def v4163_pa : Scalar.QComplex := ((999998630063753413104562544917 : Int)/10^30,(-1655255453532315404804054129 : Int)/10^30)
theorem v4163_pa_checked : Scalar.distance (sourceCoefficient 63 69 1 0) v4163_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4163_pb : Scalar.QComplex := ((-714205515447313330101947 : Int)/10^30,(-431476927326943771329115015 : Int)/10^30)
theorem v4163_pb_checked : Scalar.distance (sourceCoefficient 63 69 1 1) v4163_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4163_pg : Scalar.QComplex := ((-93086302096520831356614 : Int)/10^30,(154081820276693248143 : Int)/10^30)
theorem v4163_pg_checked : Scalar.distance (sourceCoefficient 63 69 1 2) v4163_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4163_mb : Scalar.QComplex := ((-1086550404799691641185645 : Int)/10^30,(-431476150341171049070731467 : Int)/10^30)
theorem v4163_mb_checked : Scalar.distance (sourceCoefficient 63 69 3 1) v4163_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4163_mg : Scalar.QComplex := ((-93086134470564995441067 : Int)/10^30,(234411049162871834271 : Int)/10^30)
theorem v4163_mg_checked : Scalar.distance (sourceCoefficient 63 69 3 2) v4163_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4163_upper : Scalar.QComplex := ((999994283862512828868839115466 : Int)/10^30,(-3381159904546735582958174695 : Int)/10^30)
theorem v4163_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 63 69 5) 1) 14) v4163_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4163 : Material (63 : Basis) (69 : Basis) where
  plus := ![v4163_pa,v4163_pb,v4163_pg]
  minus := ![(Primitive.Addresses.material4163 1).one,v4163_mb,v4163_mg]
  upper := v4163_upper
  lower := (Primitive.Addresses.material4163 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4163_pa_checked.trans (by decide +kernel)
    · exact v4163_pb_checked.trans (by decide +kernel)
    · exact v4163_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 63 69 Primitive.Addresses.material4163
    · exact v4163_mb_checked.trans (by decide +kernel)
    · exact v4163_mg_checked.trans (by decide +kernel)
  upper_error := v4163_upper_checked
  lower_error := reuse_lower_error 63 69 Primitive.Addresses.material4163

def v4164_pa : Scalar.QComplex := ((999998606404939513913464756902 : Int)/10^30,(-1669487400031812297375228845 : Int)/10^30)
theorem v4164_pa_checked : Scalar.distance (sourceCoefficient 63 70 1 0) v4164_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4164_pb : Scalar.QComplex := ((-720346279734032202554273 : Int)/10^30,(-431476916716645273089882054 : Int)/10^30)
theorem v4164_pb_checked : Scalar.distance (sourceCoefficient 63 70 1 1) v4164_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4164_pg : Scalar.QComplex := ((-93086299850837194423908 : Int)/10^30,(155406621290455661805 : Int)/10^30)
theorem v4164_pg_checked : Scalar.distance (sourceCoefficient 63 70 1 2) v4164_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4164_mb : Scalar.QComplex := ((-1092691157643713589024929 : Int)/10^30,(-431476134431673491848878927 : Int)/10^30)
theorem v4164_mb_checked : Scalar.distance (sourceCoefficient 63 70 3 1) v4164_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4164_mg : Scalar.QComplex := ((-93086131081638586624772 : Int)/10^30,(235735847745426447275 : Int)/10^30)
theorem v4164_mg_checked : Scalar.distance (sourceCoefficient 63 70 3 2) v4164_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4164_upper : Scalar.QComplex := ((999994235640685620671068197609 : Int)/10^30,(-3395391789016453487229274937 : Int)/10^30)
theorem v4164_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 63 70 5) 1) 14) v4164_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4164 : Material (63 : Basis) (70 : Basis) where
  plus := ![v4164_pa,v4164_pb,v4164_pg]
  minus := ![(Primitive.Addresses.material4164 1).one,v4164_mb,v4164_mg]
  upper := v4164_upper
  lower := (Primitive.Addresses.material4164 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4164_pa_checked.trans (by decide +kernel)
    · exact v4164_pb_checked.trans (by decide +kernel)
    · exact v4164_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 63 70 Primitive.Addresses.material4164
    · exact v4164_mb_checked.trans (by decide +kernel)
    · exact v4164_mg_checked.trans (by decide +kernel)
  upper_error := v4164_upper_checked
  lower_error := reuse_lower_error 63 70 Primitive.Addresses.material4164

def v4165_pa : Scalar.QComplex := ((999998565553318391835488874456 : Int)/10^30,(-1693780182189839723115900193 : Int)/10^30)
theorem v4165_pa_checked : Scalar.distance (sourceCoefficient 63 71 1 0) v4165_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4165_pb : Scalar.QComplex := ((-730828067809029690848986 : Int)/10^30,(-431476898336517165111451222 : Int)/10^30)
theorem v4165_pb_checked : Scalar.distance (sourceCoefficient 63 71 1 1) v4165_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4165_pg : Scalar.QComplex := ((-93086295966818291969783 : Int)/10^30,(157667949508321797362 : Int)/10^30)
theorem v4165_pg_checked : Scalar.distance (sourceCoefficient 63 71 1 2) v4165_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4165_mb : Scalar.QComplex := ((-1103172925954639588672763 : Int)/10^30,(-431476107006241201119706139 : Int)/10^30)
theorem v4165_mb_checked : Scalar.distance (sourceCoefficient 63 71 3 1) v4165_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4165_mg : Scalar.QComplex := ((-93086125246196724792132 : Int)/10^30,(237997171769563356415 : Int)/10^30)
theorem v4165_mg_checked : Scalar.distance (sourceCoefficient 63 71 3 2) v4165_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4165_upper : Scalar.QComplex := ((999994152861987161510696359627 : Int)/10^30,(-3419684464487043492648687411 : Int)/10^30)
theorem v4165_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 63 71 5) 1) 14) v4165_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4165 : Material (63 : Basis) (71 : Basis) where
  plus := ![v4165_pa,v4165_pb,v4165_pg]
  minus := ![(Primitive.Addresses.material4165 1).one,v4165_mb,v4165_mg]
  upper := v4165_upper
  lower := (Primitive.Addresses.material4165 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4165_pa_checked.trans (by decide +kernel)
    · exact v4165_pb_checked.trans (by decide +kernel)
    · exact v4165_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 63 71 Primitive.Addresses.material4165
    · exact v4165_mb_checked.trans (by decide +kernel)
    · exact v4165_mg_checked.trans (by decide +kernel)
  upper_error := v4165_upper_checked
  lower_error := reuse_lower_error 63 71 Primitive.Addresses.material4165

def v4166_pa : Scalar.QComplex := ((999998520553331104922444029083 : Int)/10^30,(-1720142769954781691521613722 : Int)/10^30)
theorem v4166_pa_checked : Scalar.distance (sourceCoefficient 63 72 1 0) v4166_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4166_pb : Scalar.QComplex := ((-742202930154718541339829 : Int)/10^30,(-431476878006223015050402144 : Int)/10^30)
theorem v4166_pb_checked : Scalar.distance (sourceCoefficient 63 72 1 1) v4166_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4166_pg : Scalar.QComplex := ((-93086291679357879381278 : Int)/10^30,(160121948506032744047 : Int)/10^30)
theorem v4166_pg_checked : Scalar.distance (sourceCoefficient 63 72 1 2) v4166_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4166_mb : Scalar.QComplex := ((-1114547766520819121928585 : Int)/10^30,(-431476076859960721409233869 : Int)/10^30)
theorem v4166_mb_checked : Scalar.distance (sourceCoefficient 63 72 3 1) v4166_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4166_mg : Scalar.QComplex := ((-93086118841047297608551 : Int)/10^30,(240451166153653086943 : Int)/10^30)
theorem v4166_mg_checked : Scalar.distance (sourceCoefficient 63 72 3 2) v4166_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4166_upper : Scalar.QComplex := ((999994062362632009782726523280 : Int)/10^30,(-3446046935322112062013285498 : Int)/10^30)
theorem v4166_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 63 72 5) 1) 14) v4166_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4166 : Material (63 : Basis) (72 : Basis) where
  plus := ![v4166_pa,v4166_pb,v4166_pg]
  minus := ![(Primitive.Addresses.material4166 1).one,v4166_mb,v4166_mg]
  upper := v4166_upper
  lower := (Primitive.Addresses.material4166 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4166_pa_checked.trans (by decide +kernel)
    · exact v4166_pb_checked.trans (by decide +kernel)
    · exact v4166_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 63 72 Primitive.Addresses.material4166
    · exact v4166_mb_checked.trans (by decide +kernel)
    · exact v4166_mg_checked.trans (by decide +kernel)
  upper_error := v4166_upper_checked
  lower_error := reuse_lower_error 63 72 Primitive.Addresses.material4166

def v4167_pa : Scalar.QComplex := ((999998504253948849256473048655 : Int)/10^30,(-1729592398527825838819805785 : Int)/10^30)
theorem v4167_pa_checked : Scalar.distance (sourceCoefficient 63 73 1 0) v4167_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4167_pb : Scalar.QComplex := ((-746280231813257234011983 : Int)/10^30,(-431476870621515535999624117 : Int)/10^30)
theorem v4167_pb_checked : Scalar.distance (sourceCoefficient 63 73 1 1) v4167_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4167_pg : Scalar.QComplex := ((-93086290124148371627210 : Int)/10^30,(161001580623361295379 : Int)/10^30)
theorem v4167_pg_checked : Scalar.distance (sourceCoefficient 63 73 1 2) v4167_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4167_mb : Scalar.QComplex := ((-1118625060288522105693045 : Int)/10^30,(-431476065956728295553510849 : Int)/10^30)
theorem v4167_mb_checked : Scalar.distance (sourceCoefficient 63 73 3 1) v4167_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4167_mg : Scalar.QComplex := ((-93086116526755468835427 : Int)/10^30,(241330796601378638663 : Int)/10^30)
theorem v4167_mg_checked : Scalar.distance (sourceCoefficient 63 73 3 2) v4167_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4167_upper : Scalar.QComplex := ((999994029754072376665337943367 : Int)/10^30,(-3455496521689789376237903590 : Int)/10^30)
theorem v4167_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 63 73 5) 1) 14) v4167_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4167 : Material (63 : Basis) (73 : Basis) where
  plus := ![v4167_pa,v4167_pb,v4167_pg]
  minus := ![(Primitive.Addresses.material4167 1).one,v4167_mb,v4167_mg]
  upper := v4167_upper
  lower := (Primitive.Addresses.material4167 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4167_pa_checked.trans (by decide +kernel)
    · exact v4167_pb_checked.trans (by decide +kernel)
    · exact v4167_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 63 73 Primitive.Addresses.material4167
    · exact v4167_mb_checked.trans (by decide +kernel)
    · exact v4167_mg_checked.trans (by decide +kernel)
  upper_error := v4167_upper_checked
  lower_error := reuse_lower_error 63 73 Primitive.Addresses.material4167

def v4168_pa : Scalar.QComplex := ((999998485806365490239902119970 : Int)/10^30,(-1740225553265195967046228115 : Int)/10^30)
theorem v4168_pa_checked : Scalar.distance (sourceCoefficient 63 74 1 0) v4168_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4168_pb : Scalar.QComplex := ((-750868198290815444190172 : Int)/10^30,(-431476862250478235956871960 : Int)/10^30)
theorem v4168_pb_checked : Scalar.distance (sourceCoefficient 63 74 1 1) v4168_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4168_pg : Scalar.QComplex := ((-93086288362559886740199 : Int)/10^30,(161991382953460265222 : Int)/10^30)
theorem v4168_pg_checked : Scalar.distance (sourceCoefficient 63 74 1 2) v4168_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4168_mb : Scalar.QComplex := ((-1123213017833942543437415 : Int)/10^30,(-431476053626485676637307396 : Int)/10^30)
theorem v4168_mb_checked : Scalar.distance (sourceCoefficient 63 74 3 1) v4168_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4168_mg : Scalar.QComplex := ((-93086113911012808035002 : Int)/10^30,(242320597042757441352 : Int)/10^30)
theorem v4168_mg_checked : Scalar.distance (sourceCoefficient 63 74 3 2) v4168_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4168_upper : Scalar.QComplex := ((999993992954656048718814094217 : Int)/10^30,(-3466129628751469255275177375 : Int)/10^30)
theorem v4168_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 63 74 5) 1) 14) v4168_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4168 : Material (63 : Basis) (74 : Basis) where
  plus := ![v4168_pa,v4168_pb,v4168_pg]
  minus := ![(Primitive.Addresses.material4168 1).one,v4168_mb,v4168_mg]
  upper := v4168_upper
  lower := (Primitive.Addresses.material4168 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4168_pa_checked.trans (by decide +kernel)
    · exact v4168_pb_checked.trans (by decide +kernel)
    · exact v4168_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 63 74 Primitive.Addresses.material4168
    · exact v4168_mb_checked.trans (by decide +kernel)
    · exact v4168_mg_checked.trans (by decide +kernel)
  upper_error := v4168_upper_checked
  lower_error := reuse_lower_error 63 74 Primitive.Addresses.material4168

def v4169_pa : Scalar.QComplex := ((999998459914955676052191808631 : Int)/10^30,(-1755040659581980130851131612 : Int)/10^30)
theorem v4169_pa_checked : Scalar.distance (sourceCoefficient 63 75 1 0) v4169_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4169_pb : Scalar.QComplex := ((-757260582504217484116897 : Int)/10^30,(-431476850478715182535118741 : Int)/10^30)
theorem v4169_pb_checked : Scalar.distance (sourceCoefficient 63 75 1 1) v4169_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4169_pg : Scalar.QComplex := ((-93086285887677590744846 : Int)/10^30,(163370468186761186314 : Int)/10^30)
theorem v4169_pg_checked : Scalar.distance (sourceCoefficient 63 75 1 2) v4169_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4169_mb : Scalar.QComplex := ((-1129605389508666459747410 : Int)/10^30,(-431476036338387332512510635 : Int)/10^30)
theorem v4169_mb_checked : Scalar.distance (sourceCoefficient 63 75 3 1) v4169_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4169_mg : Scalar.QComplex := ((-93086110246042988905954 : Int)/10^30,(243699679626849945894 : Int)/10^30)
theorem v4169_mg_checked : Scalar.distance (sourceCoefficient 63 75 3 2) v4169_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4169_upper : Scalar.QComplex := ((999993941493755309921318892638 : Int)/10^30,(-3480944668316668375929914567 : Int)/10^30)
theorem v4169_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 63 75 5) 1) 14) v4169_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4169 : Material (63 : Basis) (75 : Basis) where
  plus := ![v4169_pa,v4169_pb,v4169_pg]
  minus := ![(Primitive.Addresses.material4169 1).one,v4169_mb,v4169_mg]
  upper := v4169_upper
  lower := (Primitive.Addresses.material4169 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4169_pa_checked.trans (by decide +kernel)
    · exact v4169_pb_checked.trans (by decide +kernel)
    · exact v4169_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 63 75 Primitive.Addresses.material4169
    · exact v4169_mb_checked.trans (by decide +kernel)
    · exact v4169_mg_checked.trans (by decide +kernel)
  upper_error := v4169_upper_checked
  lower_error := reuse_lower_error 63 75 Primitive.Addresses.material4169

def v4170_pa : Scalar.QComplex := ((999998438022221020999324194617 : Int)/10^30,(-1767470825270793353085630443 : Int)/10^30)
theorem v4170_pa_checked : Scalar.distance (sourceCoefficient 63 76 1 0) v4170_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4170_pb : Scalar.QComplex := ((-762623918573438291151979 : Int)/10^30,(-431476840504556957047114064 : Int)/10^30)
theorem v4170_pb_checked : Scalar.distance (sourceCoefficient 63 76 1 1) v4170_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4170_pg : Scalar.QComplex := ((-93086283792813019872410 : Int)/10^30,(164527547825048236849 : Int)/10^30)
theorem v4170_pg_checked : Scalar.distance (sourceCoefficient 63 76 1 2) v4170_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4170_mb : Scalar.QComplex := ((-1134968714973622802458738 : Int)/10^30,(-431476021735915348811487397 : Int)/10^30)
theorem v4170_mb_checked : Scalar.distance (sourceCoefficient 63 76 3 1) v4170_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4170_mg : Scalar.QComplex := ((-93086107152671583137999 : Int)/10^30,(244856757026529590478 : Int)/10^30)
theorem v4170_mg_checked : Scalar.distance (sourceCoefficient 63 76 3 2) v4170_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4170_upper : Scalar.QComplex := ((999993898147714938455922399126 : Int)/10^30,(-3493374777707336033261005116 : Int)/10^30)
theorem v4170_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 63 76 5) 1) 14) v4170_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4170 : Material (63 : Basis) (76 : Basis) where
  plus := ![v4170_pa,v4170_pb,v4170_pg]
  minus := ![(Primitive.Addresses.material4170 1).one,v4170_mb,v4170_mg]
  upper := v4170_upper
  lower := (Primitive.Addresses.material4170 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4170_pa_checked.trans (by decide +kernel)
    · exact v4170_pb_checked.trans (by decide +kernel)
    · exact v4170_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 63 76 Primitive.Addresses.material4170
    · exact v4170_mb_checked.trans (by decide +kernel)
    · exact v4170_mg_checked.trans (by decide +kernel)
  upper_error := v4170_upper_checked
  lower_error := reuse_lower_error 63 76 Primitive.Addresses.material4170

def v4171_pa : Scalar.QComplex := ((999998432931841282642074925515 : Int)/10^30,(-1770348514200551920337381582 : Int)/10^30)
theorem v4171_pa_checked : Scalar.distance (sourceCoefficient 63 77 1 0) v4171_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4171_pb : Scalar.QComplex := ((-763865576418264468827169 : Int)/10^30,(-431476838182783152834926453 : Int)/10^30)
theorem v4171_pb_checked : Scalar.distance (sourceCoefficient 63 77 1 1) v4171_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4171_pg : Scalar.QComplex := ((-93086283305442068627042 : Int)/10^30,(164795421587898879980 : Int)/10^30)
theorem v4171_pg_checked : Scalar.distance (sourceCoefficient 63 77 1 2) v4171_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4171_mb : Scalar.QComplex := ((-1136210370352536793713544 : Int)/10^30,(-431476018342647611210207637 : Int)/10^30)
theorem v4171_mb_checked : Scalar.distance (sourceCoefficient 63 77 3 1) v4171_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4171_mg : Scalar.QComplex := ((-93086106434137820609425 : Int)/10^30,(245124630269059408713 : Int)/10^30)
theorem v4171_mg_checked : Scalar.distance (sourceCoefficient 63 77 3 2) v4171_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4171_upper : Scalar.QComplex := ((999993888090712750758452373266 : Int)/10^30,(-3496252453565581343962771977 : Int)/10^30)
theorem v4171_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 63 77 5) 1) 14) v4171_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4171 : Material (63 : Basis) (77 : Basis) where
  plus := ![v4171_pa,v4171_pb,v4171_pg]
  minus := ![(Primitive.Addresses.material4171 1).one,v4171_mb,v4171_mg]
  upper := v4171_upper
  lower := (Primitive.Addresses.material4171 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4171_pa_checked.trans (by decide +kernel)
    · exact v4171_pb_checked.trans (by decide +kernel)
    · exact v4171_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 63 77 Primitive.Addresses.material4171
    · exact v4171_mb_checked.trans (by decide +kernel)
    · exact v4171_mg_checked.trans (by decide +kernel)
  upper_error := v4171_upper_checked
  lower_error := reuse_lower_error 63 77 Primitive.Addresses.material4171

def v4172_pa : Scalar.QComplex := ((999998402155901494372437371013 : Int)/10^30,(-1787648076078032758163035679 : Int)/10^30)
theorem v4172_pa_checked : Scalar.distance (sourceCoefficient 63 78 1 0) v4172_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4172_pb : Scalar.QComplex := ((-771329946983894931032176 : Int)/10^30,(-431476824124762359259348869 : Int)/10^30)
theorem v4172_pb_checked : Scalar.distance (sourceCoefficient 63 78 1 1) v4172_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4172_pg : Scalar.QComplex := ((-93086280356600827200887 : Int)/10^30,(166405775879224787718 : Int)/10^30)
theorem v4172_pg_checked : Scalar.distance (sourceCoefficient 63 78 1 2) v4172_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4172_mb : Scalar.QComplex := ((-1143674726007402160644087 : Int)/10^30,(-431475997843216436709750847 : Int)/10^30)
theorem v4172_mb_checked : Scalar.distance (sourceCoefficient 63 78 3 1) v4172_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4172_mg : Scalar.QComplex := ((-93086102095634451422302 : Int)/10^30,(246734981416059636492 : Int)/10^30)
theorem v4172_mg_checked : Scalar.distance (sourceCoefficient 63 78 3 2) v4172_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4172_upper : Scalar.QComplex := ((999993827457344403098021360747 : Int)/10^30,(-3513551936560916811464062070 : Int)/10^30)
theorem v4172_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 63 78 5) 1) 14) v4172_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4172 : Material (63 : Basis) (78 : Basis) where
  plus := ![v4172_pa,v4172_pb,v4172_pg]
  minus := ![(Primitive.Addresses.material4172 1).one,v4172_mb,v4172_mg]
  upper := v4172_upper
  lower := (Primitive.Addresses.material4172 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4172_pa_checked.trans (by decide +kernel)
    · exact v4172_pb_checked.trans (by decide +kernel)
    · exact v4172_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 63 78 Primitive.Addresses.material4172
    · exact v4172_mb_checked.trans (by decide +kernel)
    · exact v4172_mg_checked.trans (by decide +kernel)
  upper_error := v4172_upper_checked
  lower_error := reuse_lower_error 63 78 Primitive.Addresses.material4172

def v4173_pa : Scalar.QComplex := ((999998392170491357888852477709 : Int)/10^30,(-1793225148208805774195069606 : Int)/10^30)
theorem v4173_pa_checked : Scalar.distance (sourceCoefficient 63 79 1 0) v4173_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4173_pb : Scalar.QComplex := ((-773736327733081826679107 : Int)/10^30,(-431476819556005544983612345 : Int)/10^30)
theorem v4173_pb_checked : Scalar.distance (sourceCoefficient 63 79 1 1) v4173_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4173_pg : Scalar.QComplex := ((-93086279399018748025046 : Int)/10^30,(166924925558332738694 : Int)/10^30)
theorem v4173_pg_checked : Scalar.distance (sourceCoefficient 63 79 1 2) v4173_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4173_mb : Scalar.QComplex := ((-1146081101917952164783967 : Int)/10^30,(-431475991197863116408400045 : Int)/10^30)
theorem v4173_mb_checked : Scalar.distance (sourceCoefficient 63 79 3 1) v4173_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4173_mg : Scalar.QComplex := ((-93086100690049937361451 : Int)/10^30,(247254130075514229190 : Int)/10^30)
theorem v4173_mg_checked : Scalar.distance (sourceCoefficient 63 79 3 2) v4173_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4173_upper : Scalar.QComplex := ((999993807846428589027095016631 : Int)/10^30,(-3519128983151383991383116705 : Int)/10^30)
theorem v4173_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 63 79 5) 1) 14) v4173_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4173 : Material (63 : Basis) (79 : Basis) where
  plus := ![v4173_pa,v4173_pb,v4173_pg]
  minus := ![(Primitive.Addresses.material4173 1).one,v4173_mb,v4173_mg]
  upper := v4173_upper
  lower := (Primitive.Addresses.material4173 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4173_pa_checked.trans (by decide +kernel)
    · exact v4173_pb_checked.trans (by decide +kernel)
    · exact v4173_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 63 79 Primitive.Addresses.material4173
    · exact v4173_mb_checked.trans (by decide +kernel)
    · exact v4173_mg_checked.trans (by decide +kernel)
  upper_error := v4173_upper_checked
  lower_error := reuse_lower_error 63 79 Primitive.Addresses.material4173

def v4174_pa : Scalar.QComplex := ((999998376510051167434603137908 : Int)/10^30,(-1801937086012027455812691040 : Int)/10^30)
theorem v4174_pa_checked : Scalar.distance (sourceCoefficient 63 80 1 0) v4174_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4174_pb : Scalar.QComplex := ((-777495332243664570034325 : Int)/10^30,(-431476812383347461618178412 : Int)/10^30)
theorem v4174_pb_checked : Scalar.distance (sourceCoefficient 63 80 1 1) v4174_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4174_pg : Scalar.QComplex := ((-93086277896421296095776 : Int)/10^30,(167735888657912485829 : Int)/10^30)
theorem v4174_pg_checked : Scalar.distance (sourceCoefficient 63 80 1 2) v4174_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4174_mb : Scalar.QComplex := ((-1149840098839204852439980 : Int)/10^30,(-431475980781356110396941717 : Int)/10^30)
theorem v4174_mb_checked : Scalar.distance (sourceCoefficient 63 80 3 1) v4174_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4174_mg : Scalar.QComplex := ((-93086098487628414402718 : Int)/10^30,(248065091576461424969 : Int)/10^30)
theorem v4174_mg_checked : Scalar.distance (sourceCoefficient 63 80 3 2) v4174_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4174_upper : Scalar.QComplex := ((999993777149997415421986921071 : Int)/10^30,(-3527840880950698626516772861 : Int)/10^30)
theorem v4174_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 63 80 5) 1) 14) v4174_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4174 : Material (63 : Basis) (80 : Basis) where
  plus := ![v4174_pa,v4174_pb,v4174_pg]
  minus := ![(Primitive.Addresses.material4174 1).one,v4174_mb,v4174_mg]
  upper := v4174_upper
  lower := (Primitive.Addresses.material4174 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4174_pa_checked.trans (by decide +kernel)
    · exact v4174_pb_checked.trans (by decide +kernel)
    · exact v4174_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 63 80 Primitive.Addresses.material4174
    · exact v4174_mb_checked.trans (by decide +kernel)
    · exact v4174_mg_checked.trans (by decide +kernel)
  upper_error := v4174_upper_checked
  lower_error := reuse_lower_error 63 80 Primitive.Addresses.material4174

def v4175_pa : Scalar.QComplex := ((999998328897324269964614254217 : Int)/10^30,(-1828169182235582358523826820 : Int)/10^30)
theorem v4175_pa_checked : Scalar.distance (sourceCoefficient 63 81 1 0) v4175_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4175_pb : Scalar.QComplex := ((-788813889472014522429266 : Int)/10^30,(-431476790522423789971667898 : Int)/10^30)
theorem v4175_pb_checked : Scalar.distance (sourceCoefficient 63 81 1 1) v4175_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4175_pg : Scalar.QComplex := ((-93086273322247516656403 : Int)/10^30,(170177740561368750538 : Int)/10^30)
theorem v4175_pg_checked : Scalar.distance (sourceCoefficient 63 81 1 2) v4175_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4175_mb : Scalar.QComplex := ((-1161158632988146115922494 : Int)/10^30,(-431475949153035459399452835 : Int)/10^30)
theorem v4175_mb_checked : Scalar.distance (sourceCoefficient 63 81 3 1) v4175_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4175_mg : Scalar.QComplex := ((-93086091806248122381732 : Int)/10^30,(250506938623398669359 : Int)/10^30)
theorem v4175_mg_checked : Scalar.distance (sourceCoefficient 63 81 3 2) v4175_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4175_upper : Scalar.QComplex := ((999993684263123106839723934649 : Int)/10^30,(-3554072855929380410534239580 : Int)/10^30)
theorem v4175_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 63 81 5) 1) 14) v4175_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4175 : Material (63 : Basis) (81 : Basis) where
  plus := ![v4175_pa,v4175_pb,v4175_pg]
  minus := ![(Primitive.Addresses.material4175 1).one,v4175_mb,v4175_mg]
  upper := v4175_upper
  lower := (Primitive.Addresses.material4175 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4175_pa_checked.trans (by decide +kernel)
    · exact v4175_pb_checked.trans (by decide +kernel)
    · exact v4175_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 63 81 Primitive.Addresses.material4175
    · exact v4175_mb_checked.trans (by decide +kernel)
    · exact v4175_mg_checked.trans (by decide +kernel)
  upper_error := v4175_upper_checked
  lower_error := reuse_lower_error 63 81 Primitive.Addresses.material4175

def v4176_pa : Scalar.QComplex := ((999998310675444987294146426896 : Int)/10^30,(-1838109424438044585662729895 : Int)/10^30)
theorem v4176_pa_checked : Scalar.distance (sourceCoefficient 63 82 1 0) v4176_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4176_pb : Scalar.QComplex := ((-793102879476970746572695 : Int)/10^30,(-431476782135140027762532035 : Int)/10^30)
theorem v4176_pb_checked : Scalar.distance (sourceCoefficient 63 82 1 1) v4176_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4176_pg : Scalar.QComplex := ((-93086271569411529189396 : Int)/10^30,(171103042106105006414 : Int)/10^30)
theorem v4176_pg_checked : Scalar.distance (sourceCoefficient 63 82 1 2) v4176_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4176_mb : Scalar.QComplex := ((-1165447614158267207145537 : Int)/10^30,(-431475937064549614821213157 : Int)/10^30)
theorem v4176_mb_checked : Scalar.distance (sourceCoefficient 63 82 3 1) v4176_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4176_mg : Scalar.QComplex := ((-93086089254919228502846 : Int)/10^30,(251432238310984359379 : Int)/10^30)
theorem v4176_mg_checked : Scalar.distance (sourceCoefficient 63 82 3 2) v4176_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4176_upper : Scalar.QComplex := ((999993648885314693796504510005 : Int)/10^30,(-3564013051877708974064775193 : Int)/10^30)
theorem v4176_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 63 82 5) 1) 14) v4176_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4176 : Material (63 : Basis) (82 : Basis) where
  plus := ![v4176_pa,v4176_pb,v4176_pg]
  minus := ![(Primitive.Addresses.material4176 1).one,v4176_mb,v4176_mg]
  upper := v4176_upper
  lower := (Primitive.Addresses.material4176 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4176_pa_checked.trans (by decide +kernel)
    · exact v4176_pb_checked.trans (by decide +kernel)
    · exact v4176_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 63 82 Primitive.Addresses.material4176
    · exact v4176_mb_checked.trans (by decide +kernel)
    · exact v4176_mg_checked.trans (by decide +kernel)
  upper_error := v4176_upper_checked
  lower_error := reuse_lower_error 63 82 Primitive.Addresses.material4176

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
