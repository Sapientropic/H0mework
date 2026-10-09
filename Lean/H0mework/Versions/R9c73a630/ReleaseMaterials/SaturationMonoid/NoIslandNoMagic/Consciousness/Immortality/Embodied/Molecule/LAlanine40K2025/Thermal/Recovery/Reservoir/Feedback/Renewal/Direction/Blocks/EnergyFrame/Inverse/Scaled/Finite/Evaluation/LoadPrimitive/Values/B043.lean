import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B028
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B029

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v689_pa : Scalar.QComplex := ((999999961473619690481541242035 : Int)/10^30,(-277583787593502905863216021 : Int)/10^30)
theorem v689_pa_checked : Scalar.distance (sourceCoefficient 7 39 1 0) v689_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v689_pb : Scalar.QComplex := ((-119771157664259344032222 : Int)/10^30,(-431477479604480775341082415 : Int)/10^30)
theorem v689_pb_checked : Scalar.distance (sourceCoefficient 7 39 1 1) v689_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v689_pg : Scalar.QComplex := ((-93086423638454844620452 : Int)/10^30,(25839283042589722948 : Int)/10^30)
theorem v689_pg_checked : Scalar.distance (sourceCoefficient 7 39 1 2) v689_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v689_mb : Scalar.QComplex := ((-492116744942356827523464 : Int)/10^30,(-431477215588580852051975009 : Int)/10^30)
theorem v689_mb_checked : Scalar.distance (sourceCoefficient 7 39 3 1) v689_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v689_mg : Scalar.QComplex := ((-93086366679987556651317 : Int)/10^30,(106168664564540902767 : Int)/10^30)
theorem v689_mg_checked : Scalar.distance (sourceCoefficient 7 39 3 2) v689_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v689_upper : Scalar.QComplex := ((999997993006710140805888391767 : Int)/10^30,(-2003492588380681453072686422 : Int)/10^30)
theorem v689_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 39 5) 1) 14) v689_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material689 : Material (7 : Basis) (39 : Basis) where
  plus := ![v689_pa,v689_pb,v689_pg]
  minus := ![(Primitive.Addresses.material689 1).one,v689_mb,v689_mg]
  upper := v689_upper
  lower := (Primitive.Addresses.material689 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v689_pa_checked.trans (by decide +kernel)
    · exact v689_pb_checked.trans (by decide +kernel)
    · exact v689_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 39 Primitive.Addresses.material689
    · exact v689_mb_checked.trans (by decide +kernel)
    · exact v689_mg_checked.trans (by decide +kernel)
  upper_error := v689_upper_checked
  lower_error := reuse_lower_error 7 39 Primitive.Addresses.material689

def v690_pa : Scalar.QComplex := ((999999954904162423995554181740 : Int)/10^30,(-300319285292127593254305104 : Int)/10^30)
theorem v690_pa_checked : Scalar.distance (sourceCoefficient 7 40 1 0) v690_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v690_pb : Scalar.QComplex := ((-129581012699209193317223 : Int)/10^30,(-431477474813508614469432222 : Int)/10^30)
theorem v690_pb_checked : Scalar.distance (sourceCoefficient 7 40 1 1) v690_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v690_pg : Scalar.QComplex := ((-93086422815891960574463 : Int)/10^30,(27955649231152889959 : Int)/10^30)
theorem v690_pg_checked : Scalar.distance (sourceCoefficient 7 40 1 2) v690_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v690_mb : Scalar.QComplex := ((-501926592190256117317322 : Int)/10^30,(-431477202332147399386163106 : Int)/10^30)
theorem v690_mb_checked : Scalar.distance (sourceCoefficient 7 40 3 1) v690_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v690_mg : Scalar.QComplex := ((-93086364031096275747848 : Int)/10^30,(108285029255249492988 : Int)/10^30)
theorem v690_mg_checked : Scalar.distance (sourceCoefficient 7 40 3 2) v690_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v690_upper : Scalar.QComplex := ((999997947197856179168063237019 : Int)/10^30,(-2026228040879165752081257128 : Int)/10^30)
theorem v690_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 40 5) 1) 14) v690_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material690 : Material (7 : Basis) (40 : Basis) where
  plus := ![v690_pa,v690_pb,v690_pg]
  minus := ![(Primitive.Addresses.material690 1).one,v690_mb,v690_mg]
  upper := v690_upper
  lower := (Primitive.Addresses.material690 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v690_pa_checked.trans (by decide +kernel)
    · exact v690_pb_checked.trans (by decide +kernel)
    · exact v690_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 40 Primitive.Addresses.material690
    · exact v690_mb_checked.trans (by decide +kernel)
    · exact v690_mg_checked.trans (by decide +kernel)
  upper_error := v690_upper_checked
  lower_error := reuse_lower_error 7 40 Primitive.Addresses.material690

def v691_pa : Scalar.QComplex := ((999999950449446548906233988864 : Int)/10^30,(-314803278964705487885542131 : Int)/10^30)
theorem v691_pa_checked : Scalar.distance (sourceCoefficient 7 41 1 0) v691_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v691_pb : Scalar.QComplex := ((-135830529591534804173394 : Int)/10^30,(-431477471606277881897153559 : Int)/10^30)
theorem v691_pb_checked : Scalar.distance (sourceCoefficient 7 41 1 1) v691_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v691_pg : Scalar.QComplex := ((-93086422262593154053311 : Int)/10^30,(29303912407382562149 : Int)/10^30)
theorem v691_pg_checked : Scalar.distance (sourceCoefficient 7 41 1 2) v691_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v691_mb : Scalar.QComplex := ((-508176103987905298229066 : Int)/10^30,(-431477193731866250727716454 : Int)/10^30)
theorem v691_mb_checked : Scalar.distance (sourceCoefficient 7 41 3 1) v691_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v691_mg : Scalar.QComplex := ((-93086362314307277678215 : Int)/10^30,(109633291451987215622 : Int)/10^30)
theorem v691_mg_checked : Scalar.distance (sourceCoefficient 7 41 3 2) v691_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v691_upper : Scalar.QComplex := ((999997917745087837627051384239 : Int)/10^30,(-2040712005291101009085135339 : Int)/10^30)
theorem v691_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 41 5) 1) 14) v691_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material691 : Material (7 : Basis) (41 : Basis) where
  plus := ![v691_pa,v691_pb,v691_pg]
  minus := ![(Primitive.Addresses.material691 1).one,v691_mb,v691_mg]
  upper := v691_upper
  lower := (Primitive.Addresses.material691 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v691_pa_checked.trans (by decide +kernel)
    · exact v691_pb_checked.trans (by decide +kernel)
    · exact v691_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 41 Primitive.Addresses.material691
    · exact v691_mb_checked.trans (by decide +kernel)
    · exact v691_mg_checked.trans (by decide +kernel)
  upper_error := v691_upper_checked
  lower_error := reuse_lower_error 7 41 Primitive.Addresses.material691

def v692_pa : Scalar.QComplex := ((999999946703141401457934833435 : Int)/10^30,(-326486928308820648655148071 : Int)/10^30)
theorem v692_pa_checked : Scalar.distance (sourceCoefficient 7 42 1 0) v692_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v692_pb : Scalar.QComplex := ((-140871760973831259833243 : Int)/10^30,(-431477468931190356411236770 : Int)/10^30)
theorem v692_pb_checked : Scalar.distance (sourceCoefficient 7 42 1 1) v692_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v692_pg : Scalar.QComplex := ((-93086421799668020945498 : Int)/10^30,(30391501540404412936 : Int)/10^30)
theorem v692_pg_checked : Scalar.distance (sourceCoefficient 7 42 1 2) v692_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v692_mb : Scalar.QComplex := ((-513217331184640861579317 : Int)/10^30,(-431477186706424087010318902 : Int)/10^30)
theorem v692_mb_checked : Scalar.distance (sourceCoefficient 7 42 3 1) v692_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v692_mg : Scalar.QComplex := ((-93086360912841878336938 : Int)/10^30,(110720879780566386408 : Int)/10^30)
theorem v692_mg_checked : Scalar.distance (sourceCoefficient 7 42 3 2) v692_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v692_upper : Scalar.QComplex := ((999997893833869434306190633783 : Int)/10^30,(-2052395630768010107309430296 : Int)/10^30)
theorem v692_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 42 5) 1) 14) v692_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material692 : Material (7 : Basis) (42 : Basis) where
  plus := ![v692_pa,v692_pb,v692_pg]
  minus := ![(Primitive.Addresses.material692 1).one,v692_mb,v692_mg]
  upper := v692_upper
  lower := (Primitive.Addresses.material692 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v692_pa_checked.trans (by decide +kernel)
    · exact v692_pb_checked.trans (by decide +kernel)
    · exact v692_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 42 Primitive.Addresses.material692
    · exact v692_mb_checked.trans (by decide +kernel)
    · exact v692_mg_checked.trans (by decide +kernel)
  upper_error := v692_upper_checked
  lower_error := reuse_lower_error 7 42 Primitive.Addresses.material692

def v693_pa : Scalar.QComplex := ((999999941530064816374857063639 : Int)/10^30,(-341964715940865696640906863 : Int)/10^30)
theorem v693_pa_checked : Scalar.distance (sourceCoefficient 7 43 1 0) v693_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v693_pb : Scalar.QComplex := ((-147550077471976190913365 : Int)/10^30,(-431477465266468731562727248 : Int)/10^30)
theorem v693_pb_checked : Scalar.distance (sourceCoefficient 7 43 1 1) v693_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v693_pg : Scalar.QComplex := ((-93086421163585135944806 : Int)/10^30,(31832273432388144227 : Int)/10^30)
theorem v693_pg_checked : Scalar.distance (sourceCoefficient 7 43 1 2) v693_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v693_mb : Scalar.QComplex := ((-519895642033653636948898 : Int)/10^30,(-431477177278617469015671070 : Int)/10^30)
theorem v693_mb_checked : Scalar.distance (sourceCoefficient 7 43 3 1) v693_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v693_mg : Scalar.QComplex := ((-93086359033437977354202 : Int)/10^30,(112161650587174014139 : Int)/10^30)
theorem v693_mg_checked : Scalar.distance (sourceCoefficient 7 43 3 2) v693_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v693_upper : Scalar.QComplex := ((999997861947543234928748093541 : Int)/10^30,(-2067873386419447738005780034 : Int)/10^30)
theorem v693_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 43 5) 1) 14) v693_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material693 : Material (7 : Basis) (43 : Basis) where
  plus := ![v693_pa,v693_pb,v693_pg]
  minus := ![(Primitive.Addresses.material693 1).one,v693_mb,v693_mg]
  upper := v693_upper
  lower := (Primitive.Addresses.material693 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v693_pa_checked.trans (by decide +kernel)
    · exact v693_pb_checked.trans (by decide +kernel)
    · exact v693_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 43 Primitive.Addresses.material693
    · exact v693_mb_checked.trans (by decide +kernel)
    · exact v693_mg_checked.trans (by decide +kernel)
  upper_error := v693_upper_checked
  lower_error := reuse_lower_error 7 43 Primitive.Addresses.material693

def v694_pa : Scalar.QComplex := ((999999939510449793207886913744 : Int)/10^30,(-347820495018045970741548381 : Int)/10^30)
theorem v694_pa_checked : Scalar.distance (sourceCoefficient 7 44 1 0) v694_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v694_pb : Scalar.QComplex := ((-150076714141439277430432 : Int)/10^30,(-431477463844043787049655914 : Int)/10^30)
theorem v694_pb_checked : Scalar.distance (sourceCoefficient 7 44 1 1) v694_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v694_pg : Scalar.QComplex := ((-93086420916149655155185 : Int)/10^30,(32377366961005725730 : Int)/10^30)
theorem v694_pg_checked : Scalar.distance (sourceCoefficient 7 44 1 2) v694_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v694_mb : Scalar.QComplex := ((-522422276534845754951148 : Int)/10^30,(-431477173675819403881076361 : Int)/10^30)
theorem v694_mb_checked : Scalar.distance (sourceCoefficient 7 44 3 1) v694_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v694_mg : Scalar.QComplex := ((-93086358315611423600332 : Int)/10^30,(112706743699302687092 : Int)/10^30)
theorem v694_mg_checked : Scalar.distance (sourceCoefficient 7 44 3 2) v694_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v694_upper : Scalar.QComplex := ((999997849821387764656085348858 : Int)/10^30,(-2073729153289460632834400006 : Int)/10^30)
theorem v694_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 44 5) 1) 14) v694_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material694 : Material (7 : Basis) (44 : Basis) where
  plus := ![v694_pa,v694_pb,v694_pg]
  minus := ![(Primitive.Addresses.material694 1).one,v694_mb,v694_mg]
  upper := v694_upper
  lower := (Primitive.Addresses.material694 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v694_pa_checked.trans (by decide +kernel)
    · exact v694_pb_checked.trans (by decide +kernel)
    · exact v694_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 44 Primitive.Addresses.material694
    · exact v694_mb_checked.trans (by decide +kernel)
    · exact v694_mg_checked.trans (by decide +kernel)
  upper_error := v694_upper_checked
  lower_error := reuse_lower_error 7 44 Primitive.Addresses.material694

def v695_pa : Scalar.QComplex := ((999999938492892465076162481075 : Int)/10^30,(-350733818282074700942581258 : Int)/10^30)
theorem v695_pa_checked : Scalar.distance (sourceCoefficient 7 45 1 0) v695_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v695_pb : Scalar.QComplex := ((-151333747454005681206223 : Int)/10^30,(-431477463129020899017234343 : Int)/10^30)
theorem v695_pb_checked : Scalar.distance (sourceCoefficient 7 45 1 1) v695_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v695_pg : Scalar.QComplex := ((-93086420791660186169633 : Int)/10^30,(32648557802589239585 : Int)/10^30)
theorem v695_pg_checked : Scalar.distance (sourceCoefficient 7 45 1 2) v695_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v695_mb : Scalar.QComplex := ((-523679308762328658261481 : Int)/10^30,(-431477171876033648018310033 : Int)/10^30)
theorem v695_mb_checked : Scalar.distance (sourceCoefficient 7 45 3 1) v695_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v695_mg : Scalar.QComplex := ((-93086357957096518663427 : Int)/10^30,(112977934332480651654 : Int)/10^30)
theorem v695_mg_checked : Scalar.distance (sourceCoefficient 7 45 3 2) v695_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v695_upper : Scalar.QComplex := ((999997843775700292964838560283 : Int)/10^30,(-2076642470458224947979435319 : Int)/10^30)
theorem v695_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 45 5) 1) 14) v695_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material695 : Material (7 : Basis) (45 : Basis) where
  plus := ![v695_pa,v695_pb,v695_pg]
  minus := ![(Primitive.Addresses.material695 1).one,v695_mb,v695_mg]
  upper := v695_upper
  lower := (Primitive.Addresses.material695 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v695_pa_checked.trans (by decide +kernel)
    · exact v695_pb_checked.trans (by decide +kernel)
    · exact v695_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 45 Primitive.Addresses.material695
    · exact v695_mb_checked.trans (by decide +kernel)
    · exact v695_mg_checked.trans (by decide +kernel)
  upper_error := v695_upper_checked
  lower_error := reuse_lower_error 7 45 Primitive.Addresses.material695

def v696_pa : Scalar.QComplex := ((999999932619504731499273774044 : Int)/10^30,(-367098060464598899824764865 : Int)/10^30)
theorem v696_pa_checked : Scalar.distance (sourceCoefficient 7 46 1 0) v696_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v696_pb : Scalar.QComplex := ((-158394549013861090849023 : Int)/10^30,(-431477459021968074970099448 : Int)/10^30)
theorem v696_pb_checked : Scalar.distance (sourceCoefficient 7 46 1 1) v696_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v696_pg : Scalar.QComplex := ((-93086420075268574058902 : Int)/10^30,(34171846567739941845 : Int)/10^30)
theorem v696_pg_checked : Scalar.distance (sourceCoefficient 7 46 1 2) v696_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v696_mb : Scalar.QComplex := ((-530740104148923340237322 : Int)/10^30,(-431477161675828613756716983 : Int)/10^30)
theorem v696_mb_checked : Scalar.distance (sourceCoefficient 7 46 3 1) v696_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v696_mg : Scalar.QComplex := ((-93086355926175575352172 : Int)/10^30,(114501221912227632742 : Int)/10^30)
theorem v696_mg_checked : Scalar.distance (sourceCoefficient 7 46 3 2) v696_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v696_upper : Scalar.QComplex := ((999997809659123852526386388142 : Int)/10^30,(-2093006678131198296330557171 : Int)/10^30)
theorem v696_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 46 5) 1) 14) v696_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material696 : Material (7 : Basis) (46 : Basis) where
  plus := ![v696_pa,v696_pb,v696_pg]
  minus := ![(Primitive.Addresses.material696 1).one,v696_mb,v696_mg]
  upper := v696_upper
  lower := (Primitive.Addresses.material696 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v696_pa_checked.trans (by decide +kernel)
    · exact v696_pb_checked.trans (by decide +kernel)
    · exact v696_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 46 Primitive.Addresses.material696
    · exact v696_mb_checked.trans (by decide +kernel)
    · exact v696_mg_checked.trans (by decide +kernel)
  upper_error := v696_upper_checked
  lower_error := reuse_lower_error 7 46 Primitive.Addresses.material696

def v697_pa : Scalar.QComplex := ((999999931166102803370546756165 : Int)/10^30,(-371036102899911214571887300 : Int)/10^30)
theorem v697_pa_checked : Scalar.distance (sourceCoefficient 7 47 1 0) v697_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v697_pb : Scalar.QComplex := ((-160093725529292162348531 : Int)/10^30,(-431477458010610822288938356 : Int)/10^30)
theorem v697_pb_checked : Scalar.distance (sourceCoefficient 7 47 1 1) v697_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v697_pg : Scalar.QComplex := ((-93086419898528090325573 : Int)/10^30,(34538424849468996785 : Int)/10^30)
theorem v697_pg_checked : Scalar.distance (sourceCoefficient 7 47 1 2) v697_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v697_mb : Scalar.QComplex := ((-532439279158917579614721 : Int)/10^30,(-431477159198158932902467214 : Int)/10^30)
theorem v697_mb_checked : Scalar.distance (sourceCoefficient 7 47 3 1) v697_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v697_mg : Scalar.QComplex := ((-93086355433094610368154 : Int)/10^30,(114867799904943762573 : Int)/10^30)
theorem v697_mg_checked : Scalar.distance (sourceCoefficient 7 47 3 2) v697_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v697_upper : Scalar.QComplex := ((999997801409020102139045019939 : Int)/10^30,(-2096944712192819122282731044 : Int)/10^30)
theorem v697_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 47 5) 1) 14) v697_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material697 : Material (7 : Basis) (47 : Basis) where
  plus := ![v697_pa,v697_pb,v697_pg]
  minus := ![(Primitive.Addresses.material697 1).one,v697_mb,v697_mg]
  upper := v697_upper
  lower := (Primitive.Addresses.material697 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v697_pa_checked.trans (by decide +kernel)
    · exact v697_pb_checked.trans (by decide +kernel)
    · exact v697_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 47 Primitive.Addresses.material697
    · exact v697_mb_checked.trans (by decide +kernel)
    · exact v697_mg_checked.trans (by decide +kernel)
  upper_error := v697_upper_checked
  lower_error := reuse_lower_error 7 47 Primitive.Addresses.material697

def v698_pa : Scalar.QComplex := ((999999920612153819571784531895 : Int)/10^30,(-398466668691907416067914573 : Int)/10^30)
theorem v698_pa_checked : Scalar.distance (sourceCoefficient 7 48 1 0) v698_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v698_pb : Scalar.QComplex := ((-171929396052564181817269 : Int)/10^30,(-431477450718455793356859394 : Int)/10^30)
theorem v698_pb_checked : Scalar.distance (sourceCoefficient 7 48 1 1) v698_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v698_pg : Scalar.QComplex := ((-93086418620713091951529 : Int)/10^30,(37091838072897020393 : Int)/10^30)
theorem v698_pg_checked : Scalar.distance (sourceCoefficient 7 48 1 2) v698_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v698_mb : Scalar.QComplex := ((-544274938982427182906893 : Int)/10^30,(-431477141692356016401515583 : Int)/10^30)
theorem v698_mb_checked : Scalar.distance (sourceCoefficient 7 48 3 1) v698_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v698_mg : Scalar.QComplex := ((-93086351951799477427177 : Int)/10^30,(117421211074922553404 : Int)/10^30)
theorem v698_mg_checked : Scalar.distance (sourceCoefficient 7 48 3 2) v698_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v698_upper : Scalar.QComplex := ((999997743512418761711795722387 : Int)/10^30,(-2124375218915051297942979164 : Int)/10^30)
theorem v698_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 48 5) 1) 14) v698_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material698 : Material (7 : Basis) (48 : Basis) where
  plus := ![v698_pa,v698_pb,v698_pg]
  minus := ![(Primitive.Addresses.material698 1).one,v698_mb,v698_mg]
  upper := v698_upper
  lower := (Primitive.Addresses.material698 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v698_pa_checked.trans (by decide +kernel)
    · exact v698_pb_checked.trans (by decide +kernel)
    · exact v698_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 48 Primitive.Addresses.material698
    · exact v698_mb_checked.trans (by decide +kernel)
    · exact v698_mg_checked.trans (by decide +kernel)
  upper_error := v698_upper_checked
  lower_error := reuse_lower_error 7 48 Primitive.Addresses.material698

def v699_pa : Scalar.QComplex := ((999999911587747171498523176109 : Int)/10^30,(-420505050909351745728136695 : Int)/10^30)
theorem v699_pa_checked : Scalar.distance (sourceCoefficient 7 49 1 0) v699_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v699_pb : Scalar.QComplex := ((-181438460826502710766375 : Int)/10^30,(-431477444546159129168819867 : Int)/10^30)
theorem v699_pb_checked : Scalar.distance (sourceCoefficient 7 49 1 1) v699_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v699_pg : Scalar.QComplex := ((-93086417534886344726636 : Int)/10^30,(39143312205224970656 : Int)/10^30)
theorem v699_pg_checked : Scalar.distance (sourceCoefficient 7 49 1 2) v699_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v699_mb : Scalar.QComplex := ((-553783994889292279517551 : Int)/10^30,(-431477127314167022911861716 : Int)/10^30)
theorem v699_mb_checked : Scalar.distance (sourceCoefficient 7 49 3 1) v699_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v699_mg : Scalar.QComplex := ((-93086349095643353271243 : Int)/10^30,(119472683506373348168 : Int)/10^30)
theorem v699_mg_checked : Scalar.distance (sourceCoefficient 7 49 3 2) v699_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v699_upper : Scalar.QComplex := ((999997696451777153540284301908 : Int)/10^30,(-2146413552733606938150559448 : Int)/10^30)
theorem v699_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 49 5) 1) 14) v699_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material699 : Material (7 : Basis) (49 : Basis) where
  plus := ![v699_pa,v699_pb,v699_pg]
  minus := ![(Primitive.Addresses.material699 1).one,v699_mb,v699_mg]
  upper := v699_upper
  lower := (Primitive.Addresses.material699 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v699_pa_checked.trans (by decide +kernel)
    · exact v699_pb_checked.trans (by decide +kernel)
    · exact v699_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 49 Primitive.Addresses.material699
    · exact v699_mb_checked.trans (by decide +kernel)
    · exact v699_mg_checked.trans (by decide +kernel)
  upper_error := v699_upper_checked
  lower_error := reuse_lower_error 7 49 Primitive.Addresses.material699

def v700_pa : Scalar.QComplex := ((999999910501512425262301734442 : Int)/10^30,(-423080331780497825549422938 : Int)/10^30)
theorem v700_pa_checked : Scalar.distance (sourceCoefficient 7 50 1 0) v700_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v700_pb : Scalar.QComplex := ((-182549636419441723699632 : Int)/10^30,(-431477443806665997376788375 : Int)/10^30)
theorem v700_pb_checked : Scalar.distance (sourceCoefficient 7 50 1 1) v700_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v700_pg : Scalar.QComplex := ((-93086417404560817661102 : Int)/10^30,(39383035884501645783 : Int)/10^30)
theorem v700_pg_checked : Scalar.distance (sourceCoefficient 7 50 1 2) v700_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v700_mb : Scalar.QComplex := ((-554895169430340568764047 : Int)/10^30,(-431477125615779675251481559 : Int)/10^30)
theorem v700_mb_checked : Scalar.distance (sourceCoefficient 7 50 3 1) v700_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v700_mg : Scalar.QComplex := ((-93086348758447136269809 : Int)/10^30,(119712406983924881373 : Int)/10^30)
theorem v700_mg_checked : Scalar.distance (sourceCoefficient 7 50 3 2) v700_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v700_upper : Scalar.QComplex := ((999997690920842869180616790568 : Int)/10^30,(-2148988827894432044584004924 : Int)/10^30)
theorem v700_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 50 5) 1) 14) v700_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material700 : Material (7 : Basis) (50 : Basis) where
  plus := ![v700_pa,v700_pb,v700_pg]
  minus := ![(Primitive.Addresses.material700 1).one,v700_mb,v700_mg]
  upper := v700_upper
  lower := (Primitive.Addresses.material700 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v700_pa_checked.trans (by decide +kernel)
    · exact v700_pb_checked.trans (by decide +kernel)
    · exact v700_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 50 Primitive.Addresses.material700
    · exact v700_mb_checked.trans (by decide +kernel)
    · exact v700_mg_checked.trans (by decide +kernel)
  upper_error := v700_upper_checked
  lower_error := reuse_lower_error 7 50 Primitive.Addresses.material700

def v701_pa : Scalar.QComplex := ((999999905657185244858297786453 : Int)/10^30,(-434379581253213038851376183 : Int)/10^30)
theorem v701_pa_checked : Scalar.distance (sourceCoefficient 7 51 1 0) v701_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v701_pb : Scalar.QComplex := ((-187425007614179050136263 : Int)/10^30,(-431477440516985448267711481 : Int)/10^30)
theorem v701_pb_checked : Scalar.distance (sourceCoefficient 7 51 1 1) v701_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v701_pg : Scalar.QComplex := ((-93086416824234436708038 : Int)/10^30,(40434842575209862469 : Int)/10^30)
theorem v701_pg_checked : Scalar.distance (sourceCoefficient 7 51 1 2) v701_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v701_mb : Scalar.QComplex := ((-559770535970908231759841 : Int)/10^30,(-431477118118874588549977609 : Int)/10^30)
theorem v701_mb_checked : Scalar.distance (sourceCoefficient 7 51 3 1) v701_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v701_mg : Scalar.QComplex := ((-93086347270459168932420 : Int)/10^30,(120764212782201867336 : Int)/10^30)
theorem v701_mg_checked : Scalar.distance (sourceCoefficient 7 51 3 2) v701_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v701_upper : Scalar.QComplex := ((999997666575043373831271427531 : Int)/10^30,(-2160288052177373231909182690 : Int)/10^30)
theorem v701_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 51 5) 1) 14) v701_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material701 : Material (7 : Basis) (51 : Basis) where
  plus := ![v701_pa,v701_pb,v701_pg]
  minus := ![(Primitive.Addresses.material701 1).one,v701_mb,v701_mg]
  upper := v701_upper
  lower := (Primitive.Addresses.material701 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v701_pa_checked.trans (by decide +kernel)
    · exact v701_pb_checked.trans (by decide +kernel)
    · exact v701_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 51 Primitive.Addresses.material701
    · exact v701_mb_checked.trans (by decide +kernel)
    · exact v701_mg_checked.trans (by decide +kernel)
  upper_error := v701_upper_checked
  lower_error := reuse_lower_error 7 51 Primitive.Addresses.material701

def v702_pa : Scalar.QComplex := ((999999894857454853298559377645 : Int)/10^30,(-458568510953868354816486023 : Int)/10^30)
theorem v702_pa_checked : Scalar.distance (sourceCoefficient 7 52 1 0) v702_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v702_pb : Scalar.QComplex := ((-197861984869116811545698 : Int)/10^30,(-431477433227657662876416736 : Int)/10^30)
theorem v702_pb_checked : Scalar.distance (sourceCoefficient 7 52 1 1) v702_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v702_pg : Scalar.QComplex := ((-93086415535284953698610 : Int)/10^30,(42686503450216275855 : Int)/10^30)
theorem v702_pg_checked : Scalar.distance (sourceCoefficient 7 52 1 2) v702_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v702_mb : Scalar.QComplex := ((-570207503049320788075174 : Int)/10^30,(-431477101822908210303234275 : Int)/10^30)
theorem v702_mb_checked : Scalar.distance (sourceCoefficient 7 52 3 1) v702_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v702_mg : Scalar.QComplex := ((-93086344038428241768513 : Int)/10^30,(123015871706506679263 : Int)/10^30)
theorem v702_mg_checked : Scalar.distance (sourceCoefficient 7 52 3 2) v702_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v702_upper : Scalar.QComplex := ((999997614027430806430961799971 : Int)/10^30,(-2184476927212104278086174052 : Int)/10^30)
theorem v702_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 52 5) 1) 14) v702_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material702 : Material (7 : Basis) (52 : Basis) where
  plus := ![v702_pa,v702_pb,v702_pg]
  minus := ![(Primitive.Addresses.material702 1).one,v702_mb,v702_mg]
  upper := v702_upper
  lower := (Primitive.Addresses.material702 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v702_pa_checked.trans (by decide +kernel)
    · exact v702_pb_checked.trans (by decide +kernel)
    · exact v702_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 52 Primitive.Addresses.material702
    · exact v702_mb_checked.trans (by decide +kernel)
    · exact v702_mg_checked.trans (by decide +kernel)
  upper_error := v702_upper_checked
  lower_error := reuse_lower_error 7 52 Primitive.Addresses.material702

def v703_pa : Scalar.QComplex := ((999999893152662914086856951779 : Int)/10^30,(-462271200439171684881969413 : Int)/10^30)
theorem v703_pa_checked : Scalar.distance (sourceCoefficient 7 53 1 0) v703_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v703_pb : Scalar.QComplex := ((-199459611802753265816076 : Int)/10^30,(-431477432082146189651996613 : Int)/10^30)
theorem v703_pb_checked : Scalar.distance (sourceCoefficient 7 53 1 1) v703_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v703_pg : Scalar.QComplex := ((-93086415332372837130352 : Int)/10^30,(43031173558041614487 : Int)/10^30)
theorem v703_pg_checked : Scalar.distance (sourceCoefficient 7 53 1 2) v703_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v703_mb : Scalar.QComplex := ((-571805128399562910323707 : Int)/10^30,(-431477099298717074322844455 : Int)/10^30)
theorem v703_mb_checked : Scalar.distance (sourceCoefficient 7 53 3 1) v703_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v703_mg : Scalar.QComplex := ((-93086343538081421065845 : Int)/10^30,(123360541510891566775 : Int)/10^30)
theorem v703_mg_checked : Scalar.distance (sourceCoefficient 7 53 3 2) v703_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v703_upper : Scalar.QComplex := ((999997605932135260039204204071 : Int)/10^30,(-2188179608240370338689962629 : Int)/10^30)
theorem v703_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 53 5) 1) 14) v703_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material703 : Material (7 : Basis) (53 : Basis) where
  plus := ![v703_pa,v703_pb,v703_pg]
  minus := ![(Primitive.Addresses.material703 1).one,v703_mb,v703_mg]
  upper := v703_upper
  lower := (Primitive.Addresses.material703 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v703_pa_checked.trans (by decide +kernel)
    · exact v703_pb_checked.trans (by decide +kernel)
    · exact v703_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 53 Primitive.Addresses.material703
    · exact v703_mb_checked.trans (by decide +kernel)
    · exact v703_mg_checked.trans (by decide +kernel)
  upper_error := v703_upper_checked
  lower_error := reuse_lower_error 7 53 Primitive.Addresses.material703

def v704_pa : Scalar.QComplex := ((999999892280679400152857031573 : Int)/10^30,(-464153670238900788382354773 : Int)/10^30)
theorem v704_pa_checked : Scalar.distance (sourceCoefficient 7 54 1 0) v704_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v704_pb : Scalar.QComplex := ((-200271855027612467290955 : Int)/10^30,(-431477431496736867106308385 : Int)/10^30)
theorem v704_pb_checked : Scalar.distance (sourceCoefficient 7 54 1 1) v704_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v704_pg : Scalar.QComplex := ((-93086415228640177016159 : Int)/10^30,(43206405931920337805 : Int)/10^30)
theorem v704_pg_checked : Scalar.distance (sourceCoefficient 7 54 1 2) v704_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v704_mb : Scalar.QComplex := ((-572617370816804958334510 : Int)/10^30,(-431477098012378648775167797 : Int)/10^30)
theorem v704_mb_checked : Scalar.distance (sourceCoefficient 7 54 3 1) v704_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v704_mg : Scalar.QComplex := ((-93086343283131153091872 : Int)/10^30,(123535773730006655049 : Int)/10^30)
theorem v704_mg_checked : Scalar.distance (sourceCoefficient 7 54 3 2) v704_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v704_upper : Scalar.QComplex := ((999997601811180946815985241500 : Int)/10^30,(-2190062073731417366606450634 : Int)/10^30)
theorem v704_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 54 5) 1) 14) v704_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material704 : Material (7 : Basis) (54 : Basis) where
  plus := ![v704_pa,v704_pb,v704_pg]
  minus := ![(Primitive.Addresses.material704 1).one,v704_mb,v704_mg]
  upper := v704_upper
  lower := (Primitive.Addresses.material704 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v704_pa_checked.trans (by decide +kernel)
    · exact v704_pb_checked.trans (by decide +kernel)
    · exact v704_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 54 Primitive.Addresses.material704
    · exact v704_mb_checked.trans (by decide +kernel)
    · exact v704_mg_checked.trans (by decide +kernel)
  upper_error := v704_upper_checked
  lower_error := reuse_lower_error 7 54 Primitive.Addresses.material704

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
