import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B066
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B067

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1601_pa : Scalar.QComplex := ((999999940955825052561616399132 : Int)/10^30,(-343639849855429560857282985 : Int)/10^30)
theorem v1601_pa_checked : Scalar.distance (sourceCoefficient 18 27 1 0) v1601_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1601_pb : Scalar.QComplex := ((-148272869822769705107019 : Int)/10^30,(-431477493458629230696497268 : Int)/10^30)
theorem v1601_pb_checked : Scalar.distance (sourceCoefficient 18 27 1 1) v1601_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1601_pg : Scalar.QComplex := ((-93086424177929188282845 : Int)/10^30,(31988206716799687992 : Int)/10^30)
theorem v1601_pg_checked : Scalar.distance (sourceCoefficient 18 27 1 2) v1601_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1601_mb : Scalar.QComplex := ((-520618458443883308677893 : Int)/10^30,(-431477204847030225543881377 : Int)/10^30)
theorem v1601_mb_checked : Scalar.distance (sourceCoefficient 18 27 3 1) v1601_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1601_mg : Scalar.QComplex := ((-93086361913217505841450 : Int)/10^30,(112317586414767625766 : Int)/10^30)
theorem v1601_mg_checked : Scalar.distance (sourceCoefficient 18 27 3 2) v1601_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1601_upper : Scalar.QComplex := ((999997858482175156802579525982 : Int)/10^30,(-2069548516848010673814357467 : Int)/10^30)
theorem v1601_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 27 5) 1) 14) v1601_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1601 : Material (18 : Basis) (27 : Basis) where
  plus := ![v1601_pa,v1601_pb,v1601_pg]
  minus := ![(Primitive.Addresses.material1601 1).one,v1601_mb,v1601_mg]
  upper := v1601_upper
  lower := (Primitive.Addresses.material1601 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1601_pa_checked.trans (by decide +kernel)
    · exact v1601_pb_checked.trans (by decide +kernel)
    · exact v1601_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 27 Primitive.Addresses.material1601
    · exact v1601_mb_checked.trans (by decide +kernel)
    · exact v1601_mg_checked.trans (by decide +kernel)
  upper_error := v1601_upper_checked
  lower_error := reuse_lower_error 18 27 Primitive.Addresses.material1601

def v1602_pa : Scalar.QComplex := ((999999938597150977993545431297 : Int)/10^30,(-350436433998668353528111292 : Int)/10^30)
theorem v1602_pa_checked : Scalar.distance (sourceCoefficient 18 28 1 0) v1602_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1602_pb : Scalar.QComplex := ((-151205443026902371163519 : Int)/10^30,(-431477492271913590917653415 : Int)/10^30)
theorem v1602_pb_checked : Scalar.distance (sourceCoefficient 18 28 1 1) v1602_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1602_pg : Scalar.QComplex := ((-93086423940138627434194 : Int)/10^30,(32620876462285204235 : Int)/10^30)
theorem v1602_pg_checked : Scalar.distance (sourceCoefficient 18 28 1 2) v1602_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1602_mb : Scalar.QComplex := ((-523551029532002796178595 : Int)/10^30,(-431477201129636430661156094 : Int)/10^30)
theorem v1602_mb_checked : Scalar.distance (sourceCoefficient 18 28 3 1) v1602_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1602_mg : Scalar.QComplex := ((-93086361129461537566667 : Int)/10^30,(112950255719478737006 : Int)/10^30)
theorem v1602_mg_checked : Scalar.distance (sourceCoefficient 18 28 3 2) v1602_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1602_upper : Scalar.QComplex := ((999997844393216945269323008701 : Int)/10^30,(-2076345086797678292523861592 : Int)/10^30)
theorem v1602_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 28 5) 1) 14) v1602_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1602 : Material (18 : Basis) (28 : Basis) where
  plus := ![v1602_pa,v1602_pb,v1602_pg]
  minus := ![(Primitive.Addresses.material1602 1).one,v1602_mb,v1602_mg]
  upper := v1602_upper
  lower := (Primitive.Addresses.material1602 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1602_pa_checked.trans (by decide +kernel)
    · exact v1602_pb_checked.trans (by decide +kernel)
    · exact v1602_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 28 Primitive.Addresses.material1602
    · exact v1602_mb_checked.trans (by decide +kernel)
    · exact v1602_mg_checked.trans (by decide +kernel)
  upper_error := v1602_upper_checked
  lower_error := reuse_lower_error 18 28 Primitive.Addresses.material1602

def v1603_pa : Scalar.QComplex := ((999999933678525779928640653636 : Int)/10^30,(-364201790277868864801469308 : Int)/10^30)
theorem v1603_pa_checked : Scalar.distance (sourceCoefficient 18 29 1 0) v1603_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1603_pb : Scalar.QComplex := ((-157144884667106635249545 : Int)/10^30,(-431477489786999832453992996 : Int)/10^30)
theorem v1603_pb_checked : Scalar.distance (sourceCoefficient 18 29 1 1) v1603_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1603_pg : Scalar.QComplex := ((-93086423443163878333625 : Int)/10^30,(33902244317010889036 : Int)/10^30)
theorem v1603_pg_checked : Scalar.distance (sourceCoefficient 18 29 1 2) v1603_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1603_mb : Scalar.QComplex := ((-529490466816312834530929 : Int)/10^30,(-431477193519252964469488651 : Int)/10^30)
theorem v1603_mb_checked : Scalar.distance (sourceCoefficient 18 29 3 1) v1603_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1603_mg : Scalar.QComplex := ((-93086359526724225550100 : Int)/10^30,(114231622668225782527 : Int)/10^30)
theorem v1603_mg_checked : Scalar.distance (sourceCoefficient 18 29 3 2) v1603_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1603_upper : Scalar.QComplex := ((999997815716842918385474734482 : Int)/10^30,(-2090110414085896740596438153 : Int)/10^30)
theorem v1603_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 29 5) 1) 14) v1603_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1603 : Material (18 : Basis) (29 : Basis) where
  plus := ![v1603_pa,v1603_pb,v1603_pg]
  minus := ![(Primitive.Addresses.material1603 1).one,v1603_mb,v1603_mg]
  upper := v1603_upper
  lower := (Primitive.Addresses.material1603 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1603_pa_checked.trans (by decide +kernel)
    · exact v1603_pb_checked.trans (by decide +kernel)
    · exact v1603_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 29 Primitive.Addresses.material1603
    · exact v1603_mb_checked.trans (by decide +kernel)
    · exact v1603_mg_checked.trans (by decide +kernel)
  upper_error := v1603_upper_checked
  lower_error := reuse_lower_error 18 29 Primitive.Addresses.material1603

def v1604_pa : Scalar.QComplex := ((999999931765135971302749423632 : Int)/10^30,(-369418087539575993807244577 : Int)/10^30)
theorem v1604_pa_checked : Scalar.distance (sourceCoefficient 18 30 1 0) v1604_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1604_pb : Scalar.QComplex := ((-159395599611445996151233 : Int)/10^30,(-431477488816875485194440458 : Int)/10^30)
theorem v1604_pb_checked : Scalar.distance (sourceCoefficient 18 30 1 1) v1604_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1604_pg : Scalar.QComplex := ((-93086423249461848341268 : Int)/10^30,(34387810799163313254 : Int)/10^30)
theorem v1604_pg_checked : Scalar.distance (sourceCoefficient 18 30 1 2) v1604_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1604_mb : Scalar.QComplex := ((-531741180085434539994247 : Int)/10^30,(-431477190606863349904818754 : Int)/10^30)
theorem v1604_mb_checked : Scalar.distance (sourceCoefficient 18 30 3 1) v1604_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1604_mg : Scalar.QComplex := ((-93086358914000262686856 : Int)/10^30,(114717188802423486087 : Int)/10^30)
theorem v1604_mg_checked : Scalar.distance (sourceCoefficient 18 30 3 2) v1604_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1604_upper : Scalar.QComplex := ((999997804800600104613435971089 : Int)/10^30,(-2095326700276204619288303995 : Int)/10^30)
theorem v1604_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 30 5) 1) 14) v1604_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1604 : Material (18 : Basis) (30 : Basis) where
  plus := ![v1604_pa,v1604_pb,v1604_pg]
  minus := ![(Primitive.Addresses.material1604 1).one,v1604_mb,v1604_mg]
  upper := v1604_upper
  lower := (Primitive.Addresses.material1604 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1604_pa_checked.trans (by decide +kernel)
    · exact v1604_pb_checked.trans (by decide +kernel)
    · exact v1604_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 30 Primitive.Addresses.material1604
    · exact v1604_mb_checked.trans (by decide +kernel)
    · exact v1604_mg_checked.trans (by decide +kernel)
  upper_error := v1604_upper_checked
  lower_error := reuse_lower_error 18 30 Primitive.Addresses.material1604

def v1605_pa : Scalar.QComplex := ((999999927604866340558831484274 : Int)/10^30,(-380513156248015896987263803 : Int)/10^30)
theorem v1605_pa_checked : Scalar.distance (sourceCoefficient 18 31 1 0) v1605_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1605_pb : Scalar.QComplex := ((-164182872200737611621789 : Int)/10^30,(-431477486701362194594903839 : Int)/10^30)
theorem v1605_pb_checked : Scalar.distance (sourceCoefficient 18 31 1 1) v1605_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1605_pg : Scalar.QComplex := ((-93086422827630406760080 : Int)/10^30,(35420611118258878938 : Int)/10^30)
theorem v1605_pg_checked : Scalar.distance (sourceCoefficient 18 31 1 2) v1605_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1605_mb : Scalar.QComplex := ((-536528449066613090700079 : Int)/10^30,(-431477184360150213202474105 : Int)/10^30)
theorem v1605_mb_checked : Scalar.distance (sourceCoefficient 18 31 3 1) v1605_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1605_mg : Scalar.QComplex := ((-93086357600908818392952 : Int)/10^30,(115749988372938756164 : Int)/10^30)
theorem v1605_mg_checked : Scalar.distance (sourceCoefficient 18 31 3 2) v1605_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1605_upper : Scalar.QComplex := ((999997781491254616105756440795 : Int)/10^30,(-2106421745279595033619380735 : Int)/10^30)
theorem v1605_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 31 5) 1) 14) v1605_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1605 : Material (18 : Basis) (31 : Basis) where
  plus := ![v1605_pa,v1605_pb,v1605_pg]
  minus := ![(Primitive.Addresses.material1605 1).one,v1605_mb,v1605_mg]
  upper := v1605_upper
  lower := (Primitive.Addresses.material1605 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1605_pa_checked.trans (by decide +kernel)
    · exact v1605_pb_checked.trans (by decide +kernel)
    · exact v1605_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 31 Primitive.Addresses.material1605
    · exact v1605_mb_checked.trans (by decide +kernel)
    · exact v1605_mg_checked.trans (by decide +kernel)
  upper_error := v1605_upper_checked
  lower_error := reuse_lower_error 18 31 Primitive.Addresses.material1605

def v1606_pa : Scalar.QComplex := ((999999925776095717343116284238 : Int)/10^30,(-385289245964802137858364547 : Int)/10^30)
theorem v1606_pa_checked : Scalar.distance (sourceCoefficient 18 32 1 0) v1606_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1606_pb : Scalar.QComplex := ((-166243647481938180942958 : Int)/10^30,(-431477485768893450260324327 : Int)/10^30)
theorem v1606_pb_checked : Scalar.distance (sourceCoefficient 18 32 1 1) v1606_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1606_pg : Scalar.QComplex := ((-93086422641928712438225 : Int)/10^30,(35865200251324789062 : Int)/10^30)
theorem v1606_pg_checked : Scalar.distance (sourceCoefficient 18 32 1 2) v1606_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1606_mb : Scalar.QComplex := ((-538589222775814311219743 : Int)/10^30,(-431477181649325562265785057 : Int)/10^30)
theorem v1606_mb_checked : Scalar.distance (sourceCoefficient 18 32 3 1) v1606_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1606_mg : Scalar.QComplex := ((-93086357031546794931688 : Int)/10^30,(116194577180211614814 : Int)/10^30)
theorem v1606_mg_checked : Scalar.distance (sourceCoefficient 18 32 3 2) v1606_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1606_upper : Scalar.QComplex := ((999997771419389148930492377066 : Int)/10^30,(-2111197824726664489350979956 : Int)/10^30)
theorem v1606_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 32 5) 1) 14) v1606_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1606 : Material (18 : Basis) (32 : Basis) where
  plus := ![v1606_pa,v1606_pb,v1606_pg]
  minus := ![(Primitive.Addresses.material1606 1).one,v1606_mb,v1606_mg]
  upper := v1606_upper
  lower := (Primitive.Addresses.material1606 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1606_pa_checked.trans (by decide +kernel)
    · exact v1606_pb_checked.trans (by decide +kernel)
    · exact v1606_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 32 Primitive.Addresses.material1606
    · exact v1606_mb_checked.trans (by decide +kernel)
    · exact v1606_mg_checked.trans (by decide +kernel)
  upper_error := v1606_upper_checked
  lower_error := reuse_lower_error 18 32 Primitive.Addresses.material1606

def v1607_pa : Scalar.QComplex := ((999999923189413241240734000496 : Int)/10^30,(-391945363051602249433245551 : Int)/10^30)
theorem v1607_pa_checked : Scalar.distance (sourceCoefficient 18 33 1 0) v1607_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1607_pb : Scalar.QComplex := ((-169115612280231165117658 : Int)/10^30,(-431477484447485470134212580 : Int)/10^30)
theorem v1607_pb_checked : Scalar.distance (sourceCoefficient 18 33 1 1) v1607_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1607_pg : Scalar.QComplex := ((-93086422378996727613631 : Int)/10^30,(36484794416929131704 : Int)/10^30)
theorem v1607_pg_checked : Scalar.distance (sourceCoefficient 18 33 1 2) v1607_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1607_mb : Scalar.QComplex := ((-541461185364427972871867 : Int)/10^30,(-431477177849541801726283654 : Int)/10^30)
theorem v1607_mb_checked : Scalar.distance (sourceCoefficient 18 33 3 1) v1607_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1607_mg : Scalar.QComplex := ((-93086356233933048577459 : Int)/10^30,(116814170888214271862 : Int)/10^30)
theorem v1607_mg_checked : Scalar.distance (sourceCoefficient 18 33 3 2) v1607_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1607_upper : Scalar.QComplex := ((999997757344856271796001749642 : Int)/10^30,(-2117853927435580790822797108 : Int)/10^30)
theorem v1607_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 33 5) 1) 14) v1607_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1607 : Material (18 : Basis) (33 : Basis) where
  plus := ![v1607_pa,v1607_pb,v1607_pg]
  minus := ![(Primitive.Addresses.material1607 1).one,v1607_mb,v1607_mg]
  upper := v1607_upper
  lower := (Primitive.Addresses.material1607 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1607_pa_checked.trans (by decide +kernel)
    · exact v1607_pb_checked.trans (by decide +kernel)
    · exact v1607_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 33 Primitive.Addresses.material1607
    · exact v1607_mb_checked.trans (by decide +kernel)
    · exact v1607_mg_checked.trans (by decide +kernel)
  upper_error := v1607_upper_checked
  lower_error := reuse_lower_error 18 33 Primitive.Addresses.material1607

def v1608_pa : Scalar.QComplex := ((999999916722160815585565958330 : Int)/10^30,(-408112326980735009577127379 : Int)/10^30)
theorem v1608_pa_checked : Scalar.distance (sourceCoefficient 18 34 1 0) v1608_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1608_pb : Scalar.QComplex := ((-176091293528985698310332 : Int)/10^30,(-431477481131795569531111467 : Int)/10^30)
theorem v1608_pb_checked : Scalar.distance (sourceCoefficient 18 34 1 1) v1608_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1608_pg : Scalar.QComplex := ((-93086421720328576944641 : Int)/10^30,(37989719342295067767 : Int)/10^30)
theorem v1608_pg_checked : Scalar.distance (sourceCoefficient 18 34 1 2) v1608_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1608_mb : Scalar.QComplex := ((-548436861154526521680045 : Int)/10^30,(-431477168514154391051698069 : Int)/10^30)
theorem v1608_mb_checked : Scalar.distance (sourceCoefficient 18 34 3 1) v1608_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1608_mg : Scalar.QComplex := ((-93086354276582711872473 : Int)/10^30,(118319094684826931030 : Int)/10^30)
theorem v1608_mg_checked : Scalar.distance (sourceCoefficient 18 34 3 2) v1608_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1608_upper : Scalar.QComplex := ((999997722974900392181247686056 : Int)/10^30,(-2134020856124028901387548851 : Int)/10^30)
theorem v1608_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 34 5) 1) 14) v1608_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1608 : Material (18 : Basis) (34 : Basis) where
  plus := ![v1608_pa,v1608_pb,v1608_pg]
  minus := ![(Primitive.Addresses.material1608 1).one,v1608_mb,v1608_mg]
  upper := v1608_upper
  lower := (Primitive.Addresses.material1608 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1608_pa_checked.trans (by decide +kernel)
    · exact v1608_pb_checked.trans (by decide +kernel)
    · exact v1608_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 34 Primitive.Addresses.material1608
    · exact v1608_mb_checked.trans (by decide +kernel)
    · exact v1608_mg_checked.trans (by decide +kernel)
  upper_error := v1608_upper_checked
  lower_error := reuse_lower_error 18 34 Primitive.Addresses.material1608

def v1609_pa : Scalar.QComplex := ((999999894441620245153490491142 : Int)/10^30,(-459474426238415887908943058 : Int)/10^30)
theorem v1609_pa_checked : Scalar.distance (sourceCoefficient 18 35 1 0) v1609_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1609_pb : Scalar.QComplex := ((-198252883706617049455497 : Int)/10^30,(-431477469600218358249937440 : Int)/10^30)
theorem v1609_pb_checked : Scalar.distance (sourceCoefficient 18 35 1 1) v1609_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1609_pg : Scalar.QComplex := ((-93086419439416444479861 : Int)/10^30,(42770833677334297689 : Int)/10^30)
theorem v1609_pg_checked : Scalar.distance (sourceCoefficient 18 35 1 2) v1609_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1609_mb : Scalar.QComplex := ((-570598433129153244609175 : Int)/10^30,(-431477137858127271177491358 : Int)/10^30)
theorem v1609_mb_checked : Scalar.distance (sourceCoefficient 18 35 3 1) v1609_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1609_mg : Scalar.QComplex := ((-93086347869785090952767 : Int)/10^30,(123100205271314344449 : Int)/10^30)
theorem v1609_mg_checked : Scalar.distance (sourceCoefficient 18 35 3 2) v1609_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1609_upper : Scalar.QComplex := ((999997612048069220486280296512 : Int)/10^30,(-2185382840429704601692316360 : Int)/10^30)
theorem v1609_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 35 5) 1) 14) v1609_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1609 : Material (18 : Basis) (35 : Basis) where
  plus := ![v1609_pa,v1609_pb,v1609_pg]
  minus := ![(Primitive.Addresses.material1609 1).one,v1609_mb,v1609_mg]
  upper := v1609_upper
  lower := (Primitive.Addresses.material1609 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1609_pa_checked.trans (by decide +kernel)
    · exact v1609_pb_checked.trans (by decide +kernel)
    · exact v1609_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 35 Primitive.Addresses.material1609
    · exact v1609_mb_checked.trans (by decide +kernel)
    · exact v1609_mg_checked.trans (by decide +kernel)
  upper_error := v1609_upper_checked
  lower_error := reuse_lower_error 18 35 Primitive.Addresses.material1609

def v1610_pa : Scalar.QComplex := ((999999886893111125887811648684 : Int)/10^30,(-475619348802228677709613309 : Int)/10^30)
theorem v1610_pa_checked : Scalar.distance (sourceCoefficient 18 36 1 0) v1610_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1610_pb : Scalar.QComplex := ((-205219054452649930459499 : Int)/10^30,(-431477465661925819918040068 : Int)/10^30)
theorem v1610_pb_checked : Scalar.distance (sourceCoefficient 18 36 1 1) v1610_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1610_pg : Scalar.QComplex := ((-93086418663263367348068 : Int)/10^30,(44273706834614187875 : Int)/10^30)
theorem v1610_pg_checked : Scalar.distance (sourceCoefficient 18 36 1 2) v1610_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1610_mb : Scalar.QComplex := ((-577564597882793300665320 : Int)/10^30,(-431477127908344590109169765 : Int)/10^30)
theorem v1610_mb_checked : Scalar.distance (sourceCoefficient 18 36 3 1) v1610_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1610_mg : Scalar.QComplex := ((-93086345796720454980039 : Int)/10^30,(124603077199220724556 : Int)/10^30)
theorem v1610_mg_checked : Scalar.distance (sourceCoefficient 18 36 3 2) v1610_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1610_upper : Scalar.QComplex := ((999997576634899654631074055394 : Int)/10^30,(-2201527725919509804066562357 : Int)/10^30)
theorem v1610_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 36 5) 1) 14) v1610_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1610 : Material (18 : Basis) (36 : Basis) where
  plus := ![v1610_pa,v1610_pb,v1610_pg]
  minus := ![(Primitive.Addresses.material1610 1).one,v1610_mb,v1610_mg]
  upper := v1610_upper
  lower := (Primitive.Addresses.material1610 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1610_pa_checked.trans (by decide +kernel)
    · exact v1610_pb_checked.trans (by decide +kernel)
    · exact v1610_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 36 Primitive.Addresses.material1610
    · exact v1610_mb_checked.trans (by decide +kernel)
    · exact v1610_mg_checked.trans (by decide +kernel)
  upper_error := v1610_upper_checked
  lower_error := reuse_lower_error 18 36 Primitive.Addresses.material1610

def v1611_pa : Scalar.QComplex := ((999999883590400299280416062119 : Int)/10^30,(-482513404839952882105289400 : Int)/10^30)
theorem v1611_pa_checked : Scalar.distance (sourceCoefficient 18 37 1 0) v1611_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1611_pb : Scalar.QComplex := ((-208193684470508330899162 : Int)/10^30,(-431477463934544131491249337 : Int)/10^30)
theorem v1611_pb_checked : Scalar.distance (sourceCoefficient 18 37 1 1) v1611_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1611_pg : Scalar.QComplex := ((-93086418323212986776529 : Int)/10^30,(44915449878079216507 : Int)/10^30)
theorem v1611_pg_checked : Scalar.distance (sourceCoefficient 18 37 1 2) v1611_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1611_mb : Scalar.QComplex := ((-580539225302408399419465 : Int)/10^30,(-431477123613991811816443765 : Int)/10^30)
theorem v1611_mb_checked : Scalar.distance (sourceCoefficient 18 37 3 1) v1611_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1611_mg : Scalar.QComplex := ((-93086344902874857548225 : Int)/10^30,(125244819710287325867 : Int)/10^30)
theorem v1611_mg_checked : Scalar.distance (sourceCoefficient 18 37 3 2) v1611_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1611_upper : Scalar.QComplex := ((999997561433678449789713361037 : Int)/10^30,(-2208421765989168105843197495 : Int)/10^30)
theorem v1611_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 37 5) 1) 14) v1611_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1611 : Material (18 : Basis) (37 : Basis) where
  plus := ![v1611_pa,v1611_pb,v1611_pg]
  minus := ![(Primitive.Addresses.material1611 1).one,v1611_mb,v1611_mg]
  upper := v1611_upper
  lower := (Primitive.Addresses.material1611 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1611_pa_checked.trans (by decide +kernel)
    · exact v1611_pb_checked.trans (by decide +kernel)
    · exact v1611_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 37 Primitive.Addresses.material1611
    · exact v1611_mb_checked.trans (by decide +kernel)
    · exact v1611_mg_checked.trans (by decide +kernel)
  upper_error := v1611_upper_checked
  lower_error := reuse_lower_error 18 37 Primitive.Addresses.material1611

def v1612_pa : Scalar.QComplex := ((999999872075879087079937380148 : Int)/10^30,(-505814418004528034129991297 : Int)/10^30)
theorem v1612_pa_checked : Scalar.distance (sourceCoefficient 18 38 1 0) v1612_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1612_pb : Scalar.QComplex := ((-218247547165768409098065 : Int)/10^30,(-431477457893833804991335830 : Int)/10^30)
theorem v1612_pb_checked : Scalar.distance (sourceCoefficient 18 38 1 1) v1612_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1612_pg : Scalar.QComplex := ((-93086417135682442131377 : Int)/10^30,(47084457930849829439 : Int)/10^30)
theorem v1612_pg_checked : Scalar.distance (sourceCoefficient 18 38 1 2) v1612_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1612_mb : Scalar.QComplex := ((-590593079041294963673096 : Int)/10^30,(-431477108897253037706339557 : Int)/10^30)
theorem v1612_mb_checked : Scalar.distance (sourceCoefficient 18 38 3 1) v1612_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1612_mg : Scalar.QComplex := ((-93086341843588494030258 : Int)/10^30,(127413825930651736549 : Int)/10^30)
theorem v1612_mg_checked : Scalar.distance (sourceCoefficient 18 38 3 2) v1612_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1612_upper : Scalar.QComplex := ((999997509703739516461066467648 : Int)/10^30,(-2231722724576602255458828021 : Int)/10^30)
theorem v1612_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 38 5) 1) 14) v1612_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1612 : Material (18 : Basis) (38 : Basis) where
  plus := ![v1612_pa,v1612_pb,v1612_pg]
  minus := ![(Primitive.Addresses.material1612 1).one,v1612_mb,v1612_mg]
  upper := v1612_upper
  lower := (Primitive.Addresses.material1612 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1612_pa_checked.trans (by decide +kernel)
    · exact v1612_pb_checked.trans (by decide +kernel)
    · exact v1612_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 38 Primitive.Addresses.material1612
    · exact v1612_mb_checked.trans (by decide +kernel)
    · exact v1612_mg_checked.trans (by decide +kernel)
  upper_error := v1612_upper_checked
  lower_error := reuse_lower_error 18 38 Primitive.Addresses.material1612

def v1613_pa : Scalar.QComplex := ((999999865147226509418729364995 : Int)/10^30,(-519331809921067730437850486 : Int)/10^30)
theorem v1613_pa_checked : Scalar.distance (sourceCoefficient 18 39 1 0) v1613_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1613_pb : Scalar.QComplex := ((-224079997471692343151536 : Int)/10^30,(-431477454246333755407638853 : Int)/10^30)
theorem v1613_pb_checked : Scalar.distance (sourceCoefficient 18 39 1 1) v1613_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1613_pg : Scalar.QComplex := ((-93086416419747088171867 : Int)/10^30,(48342743637486510588 : Int)/10^30)
theorem v1613_pg_checked : Scalar.distance (sourceCoefficient 18 39 1 2) v1613_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1613_mb : Scalar.QComplex := ((-596425524027902827197207 : Int)/10^30,(-431477100216612416051752345 : Int)/10^30)
theorem v1613_mb_checked : Scalar.distance (sourceCoefficient 18 39 3 1) v1613_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1613_mg : Scalar.QComplex := ((-93086340041809512903242 : Int)/10^30,(128672110550951176684 : Int)/10^30)
theorem v1613_mg_checked : Scalar.distance (sourceCoefficient 18 39 3 2) v1613_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1613_upper : Scalar.QComplex := ((999997479445305098481890982068 : Int)/10^30,(-2245240084402348769885256465 : Int)/10^30)
theorem v1613_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 39 5) 1) 14) v1613_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1613 : Material (18 : Basis) (39 : Basis) where
  plus := ![v1613_pa,v1613_pb,v1613_pg]
  minus := ![(Primitive.Addresses.material1613 1).one,v1613_mb,v1613_mg]
  upper := v1613_upper
  lower := (Primitive.Addresses.material1613 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1613_pa_checked.trans (by decide +kernel)
    · exact v1613_pb_checked.trans (by decide +kernel)
    · exact v1613_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 39 Primitive.Addresses.material1613
    · exact v1613_mb_checked.trans (by decide +kernel)
    · exact v1613_mg_checked.trans (by decide +kernel)
  upper_error := v1613_upper_checked
  lower_error := reuse_lower_error 18 39 Primitive.Addresses.material1613

def v1614_pa : Scalar.QComplex := ((999999853081507433458474677800 : Int)/10^30,(-542067305367183709304011736 : Int)/10^30)
theorem v1614_pa_checked : Scalar.distance (sourceCoefficient 18 40 1 0) v1614_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1614_pb : Scalar.QComplex := ((-233889851858704295091211 : Int)/10^30,(-431477447874352694278677797 : Int)/10^30)
theorem v1614_pb_checked : Scalar.distance (sourceCoefficient 18 40 1 1) v1614_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1614_pg : Scalar.QComplex := ((-93086415170828052327748 : Int)/10^30,(50459109651318018373 : Int)/10^30)
theorem v1614_pg_checked : Scalar.distance (sourceCoefficient 18 40 1 2) v1614_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1614_mb : Scalar.QComplex := ((-606235369263524985978147 : Int)/10^30,(-431477085379171210951722190 : Int)/10^30)
theorem v1614_mb_checked : Scalar.distance (sourceCoefficient 18 40 3 1) v1614_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1614_mg : Scalar.QComplex := ((-93086336966562389739075 : Int)/10^30,(130788474699002016106 : Int)/10^30)
theorem v1614_mg_checked : Scalar.distance (sourceCoefficient 18 40 3 2) v1614_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1614_upper : Scalar.QComplex := ((999997428140201401031812066979 : Int)/10^30,(-2267975525162278449039809939 : Int)/10^30)
theorem v1614_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 40 5) 1) 14) v1614_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1614 : Material (18 : Basis) (40 : Basis) where
  plus := ![v1614_pa,v1614_pb,v1614_pg]
  minus := ![(Primitive.Addresses.material1614 1).one,v1614_mb,v1614_mg]
  upper := v1614_upper
  lower := (Primitive.Addresses.material1614 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1614_pa_checked.trans (by decide +kernel)
    · exact v1614_pb_checked.trans (by decide +kernel)
    · exact v1614_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 40 Primitive.Addresses.material1614
    · exact v1614_mb_checked.trans (by decide +kernel)
    · exact v1614_mg_checked.trans (by decide +kernel)
  upper_error := v1614_upper_checked
  lower_error := reuse_lower_error 18 40 Primitive.Addresses.material1614

def v1615_pa : Scalar.QComplex := ((999999845125314610406857897565 : Int)/10^30,(-556551297539605157355549265 : Int)/10^30)
theorem v1615_pa_checked : Scalar.distance (sourceCoefficient 18 41 1 0) v1615_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1615_pb : Scalar.QComplex := ((-240139368319507395846599 : Int)/10^30,(-431477443659916264332739954 : Int)/10^30)
theorem v1615_pb_checked : Scalar.distance (sourceCoefficient 18 41 1 1) v1615_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1615_pg : Scalar.QComplex := ((-93086414345912593021002 : Int)/10^30,(51807372711177519060 : Int)/10^30)
theorem v1615_pg_checked : Scalar.distance (sourceCoefficient 18 41 1 2) v1615_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1615_mb : Scalar.QComplex := ((-612484879760478663491854 : Int)/10^30,(-431477075771685112332820229 : Int)/10^30)
theorem v1615_mb_checked : Scalar.distance (sourceCoefficient 18 41 3 1) v1615_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1615_mg : Scalar.QComplex := ((-93086334978156940441360 : Int)/10^30,(132136736544976672373 : Int)/10^30)
theorem v1615_mg_checked : Scalar.distance (sourceCoefficient 18 41 3 2) v1615_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1615_upper : Scalar.QComplex := ((999997395185963915701038908084 : Int)/10^30,(-2282459482030827933095232904 : Int)/10^30)
theorem v1615_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 41 5) 1) 14) v1615_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1615 : Material (18 : Basis) (41 : Basis) where
  plus := ![v1615_pa,v1615_pb,v1615_pg]
  minus := ![(Primitive.Addresses.material1615 1).one,v1615_mb,v1615_mg]
  upper := v1615_upper
  lower := (Primitive.Addresses.material1615 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1615_pa_checked.trans (by decide +kernel)
    · exact v1615_pb_checked.trans (by decide +kernel)
    · exact v1615_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 41 Primitive.Addresses.material1615
    · exact v1615_mb_checked.trans (by decide +kernel)
    · exact v1615_mg_checked.trans (by decide +kernel)
  upper_error := v1615_upper_checked
  lower_error := reuse_lower_error 18 41 Primitive.Addresses.material1615

def v1616_pa : Scalar.QComplex := ((999999838554510246333742455232 : Int)/10^30,(-568234945636649799743534423 : Int)/10^30)
theorem v1616_pa_checked : Scalar.distance (sourceCoefficient 18 42 1 0) v1616_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1616_pb : Scalar.QComplex := ((-245180599343081932280898 : Int)/10^30,(-431477440172356818639564983 : Int)/10^30)
theorem v1616_pb_checked : Scalar.distance (sourceCoefficient 18 42 1 1) v1616_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1616_pg : Scalar.QComplex := ((-93086413663885339918783 : Int)/10^30,(52894961747461586053 : Int)/10^30)
theorem v1616_pg_checked : Scalar.distance (sourceCoefficient 18 42 1 2) v1616_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1616_mb : Scalar.QComplex := ((-617526105897365766423169 : Int)/10^30,(-431477067933771640489452245 : Int)/10^30)
theorem v1616_mb_checked : Scalar.distance (sourceCoefficient 18 42 3 1) v1616_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1616_mg : Scalar.QComplex := ((-93086333357589586167759 : Int)/10^30,(133224324587742833823 : Int)/10^30)
theorem v1616_mg_checked : Scalar.distance (sourceCoefficient 18 42 3 2) v1616_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1616_upper : Scalar.QComplex := ((999997368450252654845737421497 : Int)/10^30,(-2294143101385838958975842088 : Int)/10^30)
theorem v1616_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 18 42 5) 1) 14) v1616_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1616 : Material (18 : Basis) (42 : Basis) where
  plus := ![v1616_pa,v1616_pb,v1616_pg]
  minus := ![(Primitive.Addresses.material1616 1).one,v1616_mb,v1616_mg]
  upper := v1616_upper
  lower := (Primitive.Addresses.material1616 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1616_pa_checked.trans (by decide +kernel)
    · exact v1616_pb_checked.trans (by decide +kernel)
    · exact v1616_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 18 42 Primitive.Addresses.material1616
    · exact v1616_mb_checked.trans (by decide +kernel)
    · exact v1616_mg_checked.trans (by decide +kernel)
  upper_error := v1616_upper_checked
  lower_error := reuse_lower_error 18 42 Primitive.Addresses.material1616

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
