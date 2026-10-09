import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B047
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B048

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1137_pa : Scalar.QComplex := ((999999835337269085755383115774 : Int)/10^30,(-573868830582977630351224426 : Int)/10^30)
theorem v1137_pa_checked : Scalar.distance (sourceCoefficient 12 52 1 0) v1137_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1137_pb : Scalar.QComplex := ((-247611482823062118021061 : Int)/10^30,(-431477419324442951854092841 : Int)/10^30)
theorem v1137_pb_checked : Scalar.distance (sourceCoefficient 12 52 1 1) v1137_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1137_pg : Scalar.QComplex := ((-93086411265292939259456 : Int)/10^30,(53419398772163859739 : Int)/10^30)
theorem v1137_pg_checked : Scalar.distance (sourceCoefficient 12 52 1 2) v1137_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1137_mb : Scalar.QComplex := ((-619956970481406223852420 : Int)/10^30,(-431477044988122576039950137 : Int)/10^30)
theorem v1137_mb_checked : Scalar.distance (sourceCoefficient 12 52 3 1) v1137_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1137_mg : Scalar.QComplex := ((-93086330506432546062728 : Int)/10^30,(133748759347296022079 : Int)/10^30)
theorem v1137_mg_checked : Scalar.distance (sourceCoefficient 12 52 3 2) v1137_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1137_upper : Scalar.QComplex := ((999997355509441970658148190344 : Int)/10^30,(-2299776972388490587323030821 : Int)/10^30)
theorem v1137_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 52 5) 1) 14) v1137_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1137 : Material (12 : Basis) (52 : Basis) where
  plus := ![v1137_pa,v1137_pb,v1137_pg]
  minus := ![(Primitive.Addresses.material1137 1).one,v1137_mb,v1137_mg]
  upper := v1137_upper
  lower := (Primitive.Addresses.material1137 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1137_pa_checked.trans (by decide +kernel)
    · exact v1137_pb_checked.trans (by decide +kernel)
    · exact v1137_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 52 Primitive.Addresses.material1137
    · exact v1137_mb_checked.trans (by decide +kernel)
    · exact v1137_mg_checked.trans (by decide +kernel)
  upper_error := v1137_upper_checked
  lower_error := reuse_lower_error 12 52 Primitive.Addresses.material1137

def v1138_pa : Scalar.QComplex := ((999999833205555820558835297390 : Int)/10^30,(-577571519847105792416087952 : Int)/10^30)
theorem v1138_pa_checked : Scalar.distance (sourceCoefficient 12 53 1 0) v1138_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1138_pb : Scalar.QComplex := ((-249209109693077167103033 : Int)/10^30,(-431477418056126848700723497 : Int)/10^30)
theorem v1138_pb_checked : Scalar.distance (sourceCoefficient 12 53 1 1) v1138_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1138_pg : Scalar.QComplex := ((-93086411029263671985912 : Int)/10^30,(53764068862832193260 : Int)/10^30)
theorem v1138_pg_checked : Scalar.distance (sourceCoefficient 12 53 1 2) v1138_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1138_mb : Scalar.QComplex := ((-621554595662052099888237 : Int)/10^30,(-431477042341126910758794542 : Int)/10^30)
theorem v1138_mb_checked : Scalar.distance (sourceCoefficient 12 53 3 1) v1138_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1138_mg : Scalar.QComplex := ((-93086329972968601791525 : Int)/10^30,(134093429105945301349 : Int)/10^30)
theorem v1138_mg_checked : Scalar.distance (sourceCoefficient 12 53 3 2) v1138_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1138_upper : Scalar.QComplex := ((999997346987226115858985669146 : Int)/10^30,(-2303479652458754330690939250 : Int)/10^30)
theorem v1138_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 53 5) 1) 14) v1138_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1138 : Material (12 : Basis) (53 : Basis) where
  plus := ![v1138_pa,v1138_pb,v1138_pg]
  minus := ![(Primitive.Addresses.material1138 1).one,v1138_mb,v1138_mg]
  upper := v1138_upper
  lower := (Primitive.Addresses.material1138 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1138_pa_checked.trans (by decide +kernel)
    · exact v1138_pb_checked.trans (by decide +kernel)
    · exact v1138_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 53 Primitive.Addresses.material1138
    · exact v1138_mb_checked.trans (by decide +kernel)
    · exact v1138_mg_checked.trans (by decide +kernel)
  upper_error := v1138_upper_checked
  lower_error := reuse_lower_error 12 53 Primitive.Addresses.material1138

def v1139_pa : Scalar.QComplex := ((999999832116522914260908014969 : Int)/10^30,(-579453989533781970639999014 : Int)/10^30)
theorem v1139_pa_checked : Scalar.distance (sourceCoefficient 12 54 1 0) v1139_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1139_pb : Scalar.QComplex := ((-250021352885416506475393 : Int)/10^30,(-431477417408282907239132825 : Int)/10^30)
theorem v1139_pb_checked : Scalar.distance (sourceCoefficient 12 54 1 1) v1139_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1139_pg : Scalar.QComplex := ((-93086410908694051527546 : Int)/10^30,(53939301227941172515 : Int)/10^30)
theorem v1139_pg_checked : Scalar.distance (sourceCoefficient 12 54 1 2) v1139_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1139_mb : Scalar.QComplex := ((-622366837992896033731578 : Int)/10^30,(-431477040992353917605653820 : Int)/10^30)
theorem v1139_mb_checked : Scalar.distance (sourceCoefficient 12 54 3 1) v1139_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1139_mg : Scalar.QComplex := ((-93086329701181387310443 : Int)/10^30,(134268661301761110357 : Int)/10^30)
theorem v1139_mg_checked : Scalar.distance (sourceCoefficient 12 54 3 2) v1139_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1139_upper : Scalar.QComplex := ((999997342649222928660505803706 : Int)/10^30,(-2305362117462141041056927387 : Int)/10^30)
theorem v1139_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 54 5) 1) 14) v1139_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1139 : Material (12 : Basis) (54 : Basis) where
  plus := ![v1139_pa,v1139_pb,v1139_pg]
  minus := ![(Primitive.Addresses.material1139 1).one,v1139_mb,v1139_mg]
  upper := v1139_upper
  lower := (Primitive.Addresses.material1139 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1139_pa_checked.trans (by decide +kernel)
    · exact v1139_pb_checked.trans (by decide +kernel)
    · exact v1139_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 54 Primitive.Addresses.material1139
    · exact v1139_mb_checked.trans (by decide +kernel)
    · exact v1139_mg_checked.trans (by decide +kernel)
  upper_error := v1139_upper_checked
  lower_error := reuse_lower_error 12 54 Primitive.Addresses.material1139

def v1140_pa : Scalar.QComplex := ((999999823107902031298182030550 : Int)/10^30,(-594797582919256080066803792 : Int)/10^30)
theorem v1140_pa_checked : Scalar.distance (sourceCoefficient 12 55 1 0) v1140_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1140_pb : Scalar.QComplex := ((-256641767170579829248674 : Int)/10^30,(-431477412051821309538508123 : Int)/10^30)
theorem v1140_pb_checked : Scalar.distance (sourceCoefficient 12 55 1 1) v1140_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1140_pg : Scalar.QComplex := ((-93086409911605652744550 : Int)/10^30,(55367581412141759719 : Int)/10^30)
theorem v1140_pg_checked : Scalar.distance (sourceCoefficient 12 55 1 2) v1140_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1140_mb : Scalar.QComplex := ((-628987245190591437517812 : Int)/10^30,(-431477029922774958655261102 : Int)/10^30)
theorem v1140_mb_checked : Scalar.distance (sourceCoefficient 12 55 3 1) v1140_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1140_mg : Scalar.QComplex := ((-93086327471551888175473 : Int)/10^30,(135696940093705328400 : Int)/10^30)
theorem v1140_mg_checked : Scalar.distance (sourceCoefficient 12 55 3 2) v1140_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1140_upper : Scalar.QComplex := ((999997307158965239570581218284 : Int)/10^30,(-2320705672447072799618537109 : Int)/10^30)
theorem v1140_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 55 5) 1) 14) v1140_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1140 : Material (12 : Basis) (55 : Basis) where
  plus := ![v1140_pa,v1140_pb,v1140_pg]
  minus := ![(Primitive.Addresses.material1140 1).one,v1140_mb,v1140_mg]
  upper := v1140_upper
  lower := (Primitive.Addresses.material1140 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1140_pa_checked.trans (by decide +kernel)
    · exact v1140_pb_checked.trans (by decide +kernel)
    · exact v1140_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 55 Primitive.Addresses.material1140
    · exact v1140_mb_checked.trans (by decide +kernel)
    · exact v1140_mg_checked.trans (by decide +kernel)
  upper_error := v1140_upper_checked
  lower_error := reuse_lower_error 12 55 Primitive.Addresses.material1140

def v1141_pa : Scalar.QComplex := ((999999820935337962087802535180 : Int)/10^30,(-598439046195743484407943264 : Int)/10^30)
theorem v1141_pa_checked : Scalar.distance (sourceCoefficient 12 56 1 0) v1141_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1141_pb : Scalar.QComplex := ((-258212976387459901249458 : Int)/10^30,(-431477410760697019759523548 : Int)/10^30)
theorem v1141_pb_checked : Scalar.distance (sourceCoefficient 12 56 1 1) v1141_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1141_pg : Scalar.QComplex := ((-93086409671214752610403 : Int)/10^30,(55706552192502930041 : Int)/10^30)
theorem v1141_pg_checked : Scalar.distance (sourceCoefficient 12 56 1 2) v1141_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1141_mb : Scalar.QComplex := ((-630558452708256398265672 : Int)/10^30,(-431477027275768360089576273 : Int)/10^30)
theorem v1141_mb_checked : Scalar.distance (sourceCoefficient 12 56 3 1) v1141_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1141_mg : Scalar.QComplex := ((-93086326938644560775376 : Int)/10^30,(136035910540405665452 : Int)/10^30)
theorem v1141_mg_checked : Scalar.distance (sourceCoefficient 12 56 3 2) v1141_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1141_upper : Scalar.QComplex := ((999997298701569141889798409273 : Int)/10^30,(-2324347126550379919972021000 : Int)/10^30)
theorem v1141_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 56 5) 1) 14) v1141_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1141 : Material (12 : Basis) (56 : Basis) where
  plus := ![v1141_pa,v1141_pb,v1141_pg]
  minus := ![(Primitive.Addresses.material1141 1).one,v1141_mb,v1141_mg]
  upper := v1141_upper
  lower := (Primitive.Addresses.material1141 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1141_pa_checked.trans (by decide +kernel)
    · exact v1141_pb_checked.trans (by decide +kernel)
    · exact v1141_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 56 Primitive.Addresses.material1141
    · exact v1141_mb_checked.trans (by decide +kernel)
    · exact v1141_mg_checked.trans (by decide +kernel)
  upper_error := v1141_upper_checked
  lower_error := reuse_lower_error 12 56 Primitive.Addresses.material1141

def v1142_pa : Scalar.QComplex := ((999999813817649901705034078530 : Int)/10^30,(-610216900399130574357707176 : Int)/10^30)
theorem v1142_pa_checked : Scalar.distance (sourceCoefficient 12 57 1 0) v1142_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1142_pb : Scalar.QComplex := ((-263294854627359556907944 : Int)/10^30,(-431477406532478744042530940 : Int)/10^30)
theorem v1142_pb_checked : Scalar.distance (sourceCoefficient 12 57 1 1) v1142_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1142_pg : Scalar.QComplex := ((-93086408883839360308051 : Int)/10^30,(56802910474081910875 : Int)/10^30)
theorem v1142_pg_checked : Scalar.distance (sourceCoefficient 12 57 1 2) v1142_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1142_mb : Scalar.QComplex := ((-635640325407178591838616 : Int)/10^30,(-431477018662119616997610108 : Int)/10^30)
theorem v1142_mb_checked : Scalar.distance (sourceCoefficient 12 57 3 1) v1142_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1142_mg : Scalar.QComplex := ((-93086325205161642790206 : Int)/10^30,(137132267734290850520 : Int)/10^30)
theorem v1142_mg_checked : Scalar.distance (sourceCoefficient 12 57 3 2) v1142_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1142_upper : Scalar.QComplex := ((999997271256383806008010865662 : Int)/10^30,(-2336124950927552817314857692 : Int)/10^30)
theorem v1142_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 57 5) 1) 14) v1142_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1142 : Material (12 : Basis) (57 : Basis) where
  plus := ![v1142_pa,v1142_pb,v1142_pg]
  minus := ![(Primitive.Addresses.material1142 1).one,v1142_mb,v1142_mg]
  upper := v1142_upper
  lower := (Primitive.Addresses.material1142 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1142_pa_checked.trans (by decide +kernel)
    · exact v1142_pb_checked.trans (by decide +kernel)
    · exact v1142_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 57 Primitive.Addresses.material1142
    · exact v1142_mb_checked.trans (by decide +kernel)
    · exact v1142_mg_checked.trans (by decide +kernel)
  upper_error := v1142_upper_checked
  lower_error := reuse_lower_error 12 57 Primitive.Addresses.material1142

def v1143_pa : Scalar.QComplex := ((999999809897608549112910155855 : Int)/10^30,(-616607449486993259713943736 : Int)/10^30)
theorem v1143_pa_checked : Scalar.distance (sourceCoefficient 12 58 1 0) v1143_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1143_pb : Scalar.QComplex := ((-266052232295211623105235 : Int)/10^30,(-431477404204890533802033185 : Int)/10^30)
theorem v1143_pb_checked : Scalar.distance (sourceCoefficient 12 58 1 1) v1143_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1143_pg : Scalar.QComplex := ((-93086408450312523168195 : Int)/10^30,(57397783807907667514 : Int)/10^30)
theorem v1143_pg_checked : Scalar.distance (sourceCoefficient 12 58 1 2) v1143_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1143_mb : Scalar.QComplex := ((-638397700039729139153669 : Int)/10^30,(-431477013955039533748342607 : Int)/10^30)
theorem v1143_mb_checked : Scalar.distance (sourceCoefficient 12 58 3 1) v1143_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1143_mg : Scalar.QComplex := ((-93086324258286072080964 : Int)/10^30,(137727140472503942793 : Int)/10^30)
theorem v1143_mg_checked : Scalar.distance (sourceCoefficient 12 58 3 2) v1143_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1143_upper : Scalar.QComplex := ((999997256306840312290529319654 : Int)/10^30,(-2342515483731807571727868228 : Int)/10^30)
theorem v1143_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 58 5) 1) 14) v1143_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1143 : Material (12 : Basis) (58 : Basis) where
  plus := ![v1143_pa,v1143_pb,v1143_pg]
  minus := ![(Primitive.Addresses.material1143 1).one,v1143_mb,v1143_mg]
  upper := v1143_upper
  lower := (Primitive.Addresses.material1143 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1143_pa_checked.trans (by decide +kernel)
    · exact v1143_pb_checked.trans (by decide +kernel)
    · exact v1143_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 58 Primitive.Addresses.material1143
    · exact v1143_mb_checked.trans (by decide +kernel)
    · exact v1143_mg_checked.trans (by decide +kernel)
  upper_error := v1143_upper_checked
  lower_error := reuse_lower_error 12 58 Primitive.Addresses.material1143

def v1144_pa : Scalar.QComplex := ((999999798912046223642618640167 : Int)/10^30,(-634173373074232444754278284 : Int)/10^30)
theorem v1144_pa_checked : Scalar.distance (sourceCoefficient 12 59 1 0) v1144_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1144_pb : Scalar.QComplex := ((-273631531719776261237304 : Int)/10^30,(-431477397685919299753739127 : Int)/10^30)
theorem v1144_pb_checked : Scalar.distance (sourceCoefficient 12 59 1 1) v1144_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1144_pg : Scalar.QComplex := ((-93086407235811713523699 : Int)/10^30,(59032932734908001421 : Int)/10^30)
theorem v1144_pg_checked : Scalar.distance (sourceCoefficient 12 59 1 2) v1144_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1144_mb : Scalar.QComplex := ((-645976991016595639006181 : Int)/10^30,(-431477000895476682585929604 : Int)/10^30)
theorem v1144_mb_checked : Scalar.distance (sourceCoefficient 12 59 3 1) v1144_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1144_mg : Scalar.QComplex := ((-93086321632725835023200 : Int)/10^30,(139362287742604101542 : Int)/10^30)
theorem v1144_mg_checked : Scalar.distance (sourceCoefficient 12 59 3 2) v1144_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1144_upper : Scalar.QComplex := ((999997215004103805089596585786 : Int)/10^30,(-2360081362196583040576043528 : Int)/10^30)
theorem v1144_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 59 5) 1) 14) v1144_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1144 : Material (12 : Basis) (59 : Basis) where
  plus := ![v1144_pa,v1144_pb,v1144_pg]
  minus := ![(Primitive.Addresses.material1144 1).one,v1144_mb,v1144_mg]
  upper := v1144_upper
  lower := (Primitive.Addresses.material1144 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1144_pa_checked.trans (by decide +kernel)
    · exact v1144_pb_checked.trans (by decide +kernel)
    · exact v1144_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 59 Primitive.Addresses.material1144
    · exact v1144_mb_checked.trans (by decide +kernel)
    · exact v1144_mg_checked.trans (by decide +kernel)
  upper_error := v1144_upper_checked
  lower_error := reuse_lower_error 12 59 Primitive.Addresses.material1144

def v1145_pa : Scalar.QComplex := ((999999785855887865523202278539 : Int)/10^30,(-654437299067873142859284249 : Int)/10^30)
theorem v1145_pa_checked : Scalar.distance (sourceCoefficient 12 60 1 0) v1145_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1145_pb : Scalar.QComplex := ((-282374958153508187860196 : Int)/10^30,(-431477389945171444971149094 : Int)/10^30)
theorem v1145_pb_checked : Scalar.distance (sourceCoefficient 12 60 1 1) v1145_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1145_pg : Scalar.QComplex := ((-93086405793146414182844 : Int)/10^30,(60919229032696972052 : Int)/10^30)
theorem v1145_pg_checked : Scalar.distance (sourceCoefficient 12 60 1 2) v1145_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1145_mb : Scalar.QComplex := ((-654720407514833541686533 : Int)/10^30,(-431476985609548487035311909 : Int)/10^30)
theorem v1145_mb_checked : Scalar.distance (sourceCoefficient 12 60 3 1) v1145_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1145_mg : Scalar.QComplex := ((-93086318562272323492239 : Int)/10^30,(141248582093083574409 : Int)/10^30)
theorem v1145_mg_checked : Scalar.distance (sourceCoefficient 12 60 3 2) v1145_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1145_upper : Scalar.QComplex := ((999997166974266956566430574381 : Int)/10^30,(-2380345235475741458431927821 : Int)/10^30)
theorem v1145_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 60 5) 1) 14) v1145_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1145 : Material (12 : Basis) (60 : Basis) where
  plus := ![v1145_pa,v1145_pb,v1145_pg]
  minus := ![(Primitive.Addresses.material1145 1).one,v1145_mb,v1145_mg]
  upper := v1145_upper
  lower := (Primitive.Addresses.material1145 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1145_pa_checked.trans (by decide +kernel)
    · exact v1145_pb_checked.trans (by decide +kernel)
    · exact v1145_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 60 Primitive.Addresses.material1145
    · exact v1145_mb_checked.trans (by decide +kernel)
    · exact v1145_mg_checked.trans (by decide +kernel)
  upper_error := v1145_upper_checked
  lower_error := reuse_lower_error 12 60 Primitive.Addresses.material1145

def v1146_pa : Scalar.QComplex := ((999999782004154207084789203142 : Int)/10^30,(-660296633388086902053486086 : Int)/10^30)
theorem v1146_pa_checked : Scalar.distance (sourceCoefficient 12 61 1 0) v1146_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1146_pb : Scalar.QComplex := ((-284903128564595912893261 : Int)/10^30,(-431477387662897123575502271 : Int)/10^30)
theorem v1146_pb_checked : Scalar.distance (sourceCoefficient 12 61 1 1) v1146_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1146_pg : Scalar.QComplex := ((-93086405367686817939897 : Int)/10^30,(61464653477521468767 : Int)/10^30)
theorem v1146_pg_checked : Scalar.distance (sourceCoefficient 12 61 1 2) v1146_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1146_mb : Scalar.QComplex := ((-657248575015067930031161 : Int)/10^30,(-431476981145577815234457253 : Int)/10^30)
theorem v1146_mb_checked : Scalar.distance (sourceCoefficient 12 61 3 1) v1146_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1146_mg : Scalar.QComplex := ((-93086317666136154788903 : Int)/10^30,(141794005967669153619 : Int)/10^30)
theorem v1146_mg_checked : Scalar.distance (sourceCoefficient 12 61 3 2) v1146_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1146_upper : Scalar.QComplex := ((999997153009859552801149635022 : Int)/10^30,(-2386204554421422165509647311 : Int)/10^30)
theorem v1146_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 61 5) 1) 14) v1146_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1146 : Material (12 : Basis) (61 : Basis) where
  plus := ![v1146_pa,v1146_pb,v1146_pg]
  minus := ![(Primitive.Addresses.material1146 1).one,v1146_mb,v1146_mg]
  upper := v1146_upper
  lower := (Primitive.Addresses.material1146 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1146_pa_checked.trans (by decide +kernel)
    · exact v1146_pb_checked.trans (by decide +kernel)
    · exact v1146_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 61 Primitive.Addresses.material1146
    · exact v1146_mb_checked.trans (by decide +kernel)
    · exact v1146_mg_checked.trans (by decide +kernel)
  upper_error := v1146_upper_checked
  lower_error := reuse_lower_error 12 61 Primitive.Addresses.material1146

def v1147_pa : Scalar.QComplex := ((999999776346570450093346799152 : Int)/10^30,(-668809994751092783761912931 : Int)/10^30)
theorem v1147_pa_checked : Scalar.distance (sourceCoefficient 12 62 1 0) v1147_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1147_pb : Scalar.QComplex := ((-288576451677805260867419 : Int)/10^30,(-431477384311653402222351269 : Int)/10^30)
theorem v1147_pb_checked : Scalar.distance (sourceCoefficient 12 62 1 1) v1147_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1147_pg : Scalar.QComplex := ((-93086404742868080040137 : Int)/10^30,(62257131791496738132 : Int)/10^30)
theorem v1147_pg_checked : Scalar.distance (sourceCoefficient 12 62 1 2) v1147_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1147_mb : Scalar.QComplex := ((-660921893868558806684298 : Int)/10^30,(-431476974624422935334420973 : Int)/10^30)
theorem v1147_mb_checked : Scalar.distance (sourceCoefficient 12 62 3 1) v1147_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1147_mg : Scalar.QComplex := ((-93086316357444556475372 : Int)/10^30,(142586483447378098626 : Int)/10^30)
theorem v1147_mg_checked : Scalar.distance (sourceCoefficient 12 62 3 2) v1147_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1147_upper : Scalar.QComplex := ((999997132658994835677746378096 : Int)/10^30,(-2394717893340300034118070355 : Int)/10^30)
theorem v1147_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 62 5) 1) 14) v1147_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1147 : Material (12 : Basis) (62 : Basis) where
  plus := ![v1147_pa,v1147_pb,v1147_pg]
  minus := ![(Primitive.Addresses.material1147 1).one,v1147_mb,v1147_mg]
  upper := v1147_upper
  lower := (Primitive.Addresses.material1147 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1147_pa_checked.trans (by decide +kernel)
    · exact v1147_pb_checked.trans (by decide +kernel)
    · exact v1147_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 62 Primitive.Addresses.material1147
    · exact v1147_mb_checked.trans (by decide +kernel)
    · exact v1147_mg_checked.trans (by decide +kernel)
  upper_error := v1147_upper_checked
  lower_error := reuse_lower_error 12 62 Primitive.Addresses.material1147

def v1148_pa : Scalar.QComplex := ((999999759455910120812844689323 : Int)/10^30,(-693605162824582163457824204 : Int)/10^30)
theorem v1148_pa_checked : Scalar.distance (sourceCoefficient 12 63 1 0) v1148_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1148_pb : Scalar.QComplex := ((-299275006454732018540357 : Int)/10^30,(-431477374313585948347346016 : Int)/10^30)
theorem v1148_pb_checked : Scalar.distance (sourceCoefficient 12 63 1 1) v1148_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1148_pg : Scalar.QComplex := ((-93086402878237052659526 : Int)/10^30,(64565225155897587628 : Int)/10^30)
theorem v1148_pg_checked : Scalar.distance (sourceCoefficient 12 63 1 2) v1148_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1148_mb : Scalar.QComplex := ((-671620436034042756347783 : Int)/10^30,(-431476955393988276729296030 : Int)/10^30)
theorem v1148_mb_checked : Scalar.distance (sourceCoefficient 12 63 3 1) v1148_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1148_mg : Scalar.QComplex := ((-93086312501033602570407 : Int)/10^30,(144894574343277706713 : Int)/10^30)
theorem v1148_mg_checked : Scalar.distance (sourceCoefficient 12 63 3 2) v1148_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1148_upper : Scalar.QComplex := ((999997072974148968285296885598 : Int)/10^30,(-2419512995332551793792804399 : Int)/10^30)
theorem v1148_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 63 5) 1) 14) v1148_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1148 : Material (12 : Basis) (63 : Basis) where
  plus := ![v1148_pa,v1148_pb,v1148_pg]
  minus := ![(Primitive.Addresses.material1148 1).one,v1148_mb,v1148_mg]
  upper := v1148_upper
  lower := (Primitive.Addresses.material1148 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1148_pa_checked.trans (by decide +kernel)
    · exact v1148_pb_checked.trans (by decide +kernel)
    · exact v1148_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 63 Primitive.Addresses.material1148
    · exact v1148_mb_checked.trans (by decide +kernel)
    · exact v1148_mg_checked.trans (by decide +kernel)
  upper_error := v1148_upper_checked
  lower_error := reuse_lower_error 12 63 Primitive.Addresses.material1148

def v1149_pa : Scalar.QComplex := ((999999734248535734566328999627 : Int)/10^30,(-729042425313524934903739491 : Int)/10^30)
theorem v1149_pa_checked : Scalar.distance (sourceCoefficient 12 64 1 0) v1149_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1149_pb : Scalar.QComplex := ((-314565384168615639026137 : Int)/10^30,(-431477359410359798987409291 : Int)/10^30)
theorem v1149_pb_checked : Scalar.distance (sourceCoefficient 12 64 1 1) v1149_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1149_pg : Scalar.QComplex := ((-93086400097402960031965 : Int)/10^30,(67863952925660658550 : Int)/10^30)
theorem v1149_pg_checked : Scalar.distance (sourceCoefficient 12 64 1 2) v1149_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1149_mb : Scalar.QComplex := ((-686910795193806998662928 : Int)/10^30,(-431476927295860362488231837 : Int)/10^30)
theorem v1149_mb_checked : Scalar.distance (sourceCoefficient 12 64 3 1) v1149_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1149_mg : Scalar.QComplex := ((-93086306873547049252540 : Int)/10^30,(148193298485039091825 : Int)/10^30)
theorem v1149_mg_checked : Scalar.distance (sourceCoefficient 12 64 3 2) v1149_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1149_upper : Scalar.QComplex := ((999996986605311912886658671302 : Int)/10^30,(-2454950161536213445707252010 : Int)/10^30)
theorem v1149_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 64 5) 1) 14) v1149_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1149 : Material (12 : Basis) (64 : Basis) where
  plus := ![v1149_pa,v1149_pb,v1149_pg]
  minus := ![(Primitive.Addresses.material1149 1).one,v1149_mb,v1149_mg]
  upper := v1149_upper
  lower := (Primitive.Addresses.material1149 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1149_pa_checked.trans (by decide +kernel)
    · exact v1149_pb_checked.trans (by decide +kernel)
    · exact v1149_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 64 Primitive.Addresses.material1149
    · exact v1149_mb_checked.trans (by decide +kernel)
    · exact v1149_mg_checked.trans (by decide +kernel)
  upper_error := v1149_upper_checked
  lower_error := reuse_lower_error 12 64 Primitive.Addresses.material1149

def v1150_pa : Scalar.QComplex := ((999999707380546020527745076640 : Int)/10^30,(-765009034151100507513357854 : Int)/10^30)
theorem v1150_pa_checked : Scalar.distance (sourceCoefficient 12 65 1 0) v1150_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1150_pb : Scalar.QComplex := ((-330084162433088145734455 : Int)/10^30,(-431477343545781345246821191 : Int)/10^30)
theorem v1150_pb_checked : Scalar.distance (sourceCoefficient 12 65 1 1) v1150_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1150_pg : Scalar.QComplex := ((-93086397135578007963913 : Int)/10^30,(71211955603297866201 : Int)/10^30)
theorem v1150_pg_checked : Scalar.distance (sourceCoefficient 12 65 1 2) v1150_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1150_mb : Scalar.QComplex := ((-702429553989512422815539 : Int)/10^30,(-431476898039281113442641689 : Int)/10^30)
theorem v1150_mb_checked : Scalar.distance (sourceCoefficient 12 65 3 1) v1150_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1150_mg : Scalar.QComplex := ((-93086301022547677649441 : Int)/10^30,(151541297360140353321 : Int)/10^30)
theorem v1150_mg_checked : Scalar.distance (sourceCoefficient 12 65 3 2) v1150_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1150_upper : Scalar.QComplex := ((999996897662258227172819853276 : Int)/10^30,(-2490916670434037287963575703 : Int)/10^30)
theorem v1150_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 65 5) 1) 14) v1150_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1150 : Material (12 : Basis) (65 : Basis) where
  plus := ![v1150_pa,v1150_pb,v1150_pg]
  minus := ![(Primitive.Addresses.material1150 1).one,v1150_mb,v1150_mg]
  upper := v1150_upper
  lower := (Primitive.Addresses.material1150 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1150_pa_checked.trans (by decide +kernel)
    · exact v1150_pb_checked.trans (by decide +kernel)
    · exact v1150_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 65 Primitive.Addresses.material1150
    · exact v1150_mb_checked.trans (by decide +kernel)
    · exact v1150_mg_checked.trans (by decide +kernel)
  upper_error := v1150_upper_checked
  lower_error := reuse_lower_error 12 65 Primitive.Addresses.material1150

def v1151_pa : Scalar.QComplex := ((999999693771237541972612240077 : Int)/10^30,(-782596595405321079745176083 : Int)/10^30)
theorem v1151_pa_checked : Scalar.distance (sourceCoefficient 12 66 1 0) v1151_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1151_pb : Scalar.QComplex := ((-337672797175376920872779 : Int)/10^30,(-431477335517115643212387680 : Int)/10^30)
theorem v1151_pb_checked : Scalar.distance (sourceCoefficient 12 66 1 1) v1151_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1151_pg : Scalar.QComplex := ((-93086395636109800852220 : Int)/10^30,(72849118611867706252 : Int)/10^30)
theorem v1151_pg_checked : Scalar.distance (sourceCoefficient 12 66 1 2) v1151_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1151_mb : Scalar.QComplex := ((-710018178977828762483252 : Int)/10^30,(-431476883461968397673508438 : Int)/10^30)
theorem v1151_mb_checked : Scalar.distance (sourceCoefficient 12 66 3 1) v1151_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1151_mg : Scalar.QComplex := ((-93086298110282087547250 : Int)/10^30,(153178458465146054039 : Int)/10^30)
theorem v1151_mg_checked : Scalar.distance (sourceCoefficient 12 66 3 2) v1151_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1151_upper : Scalar.QComplex := ((999996853698434824392674450147 : Int)/10^30,(-2508504182005219544940596744 : Int)/10^30)
theorem v1151_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 66 5) 1) 14) v1151_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1151 : Material (12 : Basis) (66 : Basis) where
  plus := ![v1151_pa,v1151_pb,v1151_pg]
  minus := ![(Primitive.Addresses.material1151 1).one,v1151_mb,v1151_mg]
  upper := v1151_upper
  lower := (Primitive.Addresses.material1151 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1151_pa_checked.trans (by decide +kernel)
    · exact v1151_pb_checked.trans (by decide +kernel)
    · exact v1151_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 66 Primitive.Addresses.material1151
    · exact v1151_mb_checked.trans (by decide +kernel)
    · exact v1151_mg_checked.trans (by decide +kernel)
  upper_error := v1151_upper_checked
  lower_error := reuse_lower_error 12 66 Primitive.Addresses.material1151

def v1152_pa : Scalar.QComplex := ((999999670235581451957605585895 : Int)/10^30,(-812113741018776906460058748 : Int)/10^30)
theorem v1152_pa_checked : Scalar.distance (sourceCoefficient 12 67 1 0) v1152_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1152_pb : Scalar.QComplex := ((-350408777396347775278340 : Int)/10^30,(-431477321642682602673968762 : Int)/10^30)
theorem v1152_pb_checked : Scalar.distance (sourceCoefficient 12 67 1 1) v1152_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1152_pg : Scalar.QComplex := ((-93086393044058130904875 : Int)/10^30,(75596763822077166906 : Int)/10^30)
theorem v1152_pg_checked : Scalar.distance (sourceCoefficient 12 67 1 2) v1152_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1152_mb : Scalar.QComplex := ((-722754142483601284853574 : Int)/10^30,(-431476858596963199778606365 : Int)/10^30)
theorem v1152_mb_checked : Scalar.distance (sourceCoefficient 12 67 3 1) v1152_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1152_mg : Scalar.QComplex := ((-93086293147137315674916 : Int)/10^30,(155926100415457779852 : Int)/10^30)
theorem v1152_mg_checked : Scalar.distance (sourceCoefficient 12 67 3 2) v1152_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1152_upper : Scalar.QComplex := ((999996779218898233680390581040 : Int)/10^30,(-2538021243035947034579055349 : Int)/10^30)
theorem v1152_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 12 67 5) 1) 14) v1152_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1152 : Material (12 : Basis) (67 : Basis) where
  plus := ![v1152_pa,v1152_pb,v1152_pg]
  minus := ![(Primitive.Addresses.material1152 1).one,v1152_mb,v1152_mg]
  upper := v1152_upper
  lower := (Primitive.Addresses.material1152 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1152_pa_checked.trans (by decide +kernel)
    · exact v1152_pb_checked.trans (by decide +kernel)
    · exact v1152_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 12 67 Primitive.Addresses.material1152
    · exact v1152_mb_checked.trans (by decide +kernel)
    · exact v1152_mg_checked.trans (by decide +kernel)
  upper_error := v1152_upper_checked
  lower_error := reuse_lower_error 12 67 Primitive.Addresses.material1152

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
