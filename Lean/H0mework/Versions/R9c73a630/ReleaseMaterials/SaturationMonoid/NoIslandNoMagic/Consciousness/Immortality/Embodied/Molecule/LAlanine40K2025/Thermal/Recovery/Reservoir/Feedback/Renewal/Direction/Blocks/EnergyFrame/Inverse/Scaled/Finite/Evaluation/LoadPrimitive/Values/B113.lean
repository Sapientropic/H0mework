import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B075
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B076

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1809_pa : Scalar.QComplex := ((999999310282183584372175911806 : Int)/10^30,(-1174493574746405058865643865 : Int)/10^30)
theorem v1809_pa_checked : Scalar.distance (sourceCoefficient 20 80 1 0) v1809_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1809_pb : Scalar.QComplex := ((-506767497666372050777996 : Int)/10^30,(-431477156653854453021209272 : Int)/10^30)
theorem v1809_pb_checked : Scalar.distance (sourceCoefficient 20 80 1 1) v1809_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1809_pg : Scalar.QComplex := ((-93086358493426273231882 : Int)/10^30,(109329405353508338485 : Int)/10^30)
theorem v1809_pg_checked : Scalar.distance (sourceCoefficient 20 80 1 2) v1809_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1809_mb : Scalar.QComplex := ((-879112662156200185114420 : Int)/10^30,(-431476558677663025320589101 : Int)/10^30)
theorem v1809_mb_checked : Scalar.distance (sourceCoefficient 20 80 3 1) v1809_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1809_mg : Scalar.QComplex := ((-93086229486767942933032 : Int)/10^30,(189658699571045660923 : Int)/10^30)
theorem v1809_mg_checked : Scalar.distance (sourceCoefficient 20 80 3 2) v1809_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1809_upper : Scalar.QComplex := ((999995793831318302223397259062 : Int)/10^30,(-2900399915794470972917323540 : Int)/10^30)
theorem v1809_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 80 5) 1) 14) v1809_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1809 : Material (20 : Basis) (80 : Basis) where
  plus := ![v1809_pa,v1809_pb,v1809_pg]
  minus := ![(Primitive.Addresses.material1809 1).one,v1809_mb,v1809_mg]
  upper := v1809_upper
  lower := (Primitive.Addresses.material1809 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1809_pa_checked.trans (by decide +kernel)
    · exact v1809_pb_checked.trans (by decide +kernel)
    · exact v1809_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 80 Primitive.Addresses.material1809
    · exact v1809_mb_checked.trans (by decide +kernel)
    · exact v1809_mg_checked.trans (by decide +kernel)
  upper_error := v1809_upper_checked
  lower_error := reuse_lower_error 20 80 Primitive.Addresses.material1809

def v1810_pa : Scalar.QComplex := ((999999279128642038315480616950 : Int)/10^30,(-1200725695680680562840655988 : Int)/10^30)
theorem v1810_pa_checked : Scalar.distance (sourceCoefficient 20 81 1 0) v1810_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1810_pb : Scalar.QComplex := ((-518086062002801955423517 : Int)/10^30,(-431477139527442857176277776 : Int)/10^30)
theorem v1810_pb_checked : Scalar.distance (sourceCoefficient 20 81 1 1) v1810_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1810_pg : Scalar.QComplex := ((-93086355196024792973234 : Int)/10^30,(111771259173825185150 : Int)/10^30)
theorem v1810_pg_checked : Scalar.distance (sourceCoefficient 20 81 1 2) v1810_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1810_mb : Scalar.QComplex := ((-890431207498889441092998 : Int)/10^30,(-431476531783846553296592770 : Int)/10^30)
theorem v1810_mb_checked : Scalar.distance (sourceCoefficient 20 81 3 1) v1810_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1810_mg : Scalar.QComplex := ((-93086224082157820527743 : Int)/10^30,(192100549636639764038 : Int)/10^30)
theorem v1810_mg_checked : Scalar.distance (sourceCoefficient 20 81 3 2) v1810_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1810_upper : Scalar.QComplex := ((999995717403562182569259938914 : Int)/10^30,(-2926631943890897305391290498 : Int)/10^30)
theorem v1810_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 81 5) 1) 14) v1810_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1810 : Material (20 : Basis) (81 : Basis) where
  plus := ![v1810_pa,v1810_pb,v1810_pg]
  minus := ![(Primitive.Addresses.material1810 1).one,v1810_mb,v1810_mg]
  upper := v1810_upper
  lower := (Primitive.Addresses.material1810 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1810_pa_checked.trans (by decide +kernel)
    · exact v1810_pb_checked.trans (by decide +kernel)
    · exact v1810_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 81 Primitive.Addresses.material1810
    · exact v1810_mb_checked.trans (by decide +kernel)
    · exact v1810_mg_checked.trans (by decide +kernel)
  upper_error := v1810_upper_checked
  lower_error := reuse_lower_error 20 81 Primitive.Addresses.material1810

def v1811_pa : Scalar.QComplex := ((999999267143713412667930789614 : Int)/10^30,(-1210665947359686559647490830 : Int)/10^30)
theorem v1811_pa_checked : Scalar.distance (sourceCoefficient 20 82 1 0) v1811_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1811_pb : Scalar.QComplex := ((-522375054733701777594278 : Int)/10^30,(-431477132934228333497164837 : Int)/10^30)
theorem v1811_pb_checked : Scalar.distance (sourceCoefficient 20 82 1 1) v1811_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1811_pg : Scalar.QComplex := ((-93086353927001682549493 : Int)/10^30,(112696561453676109371 : Int)/10^30)
theorem v1811_pg_checked : Scalar.distance (sourceCoefficient 20 82 1 2) v1811_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1811_mb : Scalar.QComplex := ((-894720192943154066322402 : Int)/10^30,(-431476521489426926867852340 : Int)/10^30)
theorem v1811_mb_checked : Scalar.distance (sourceCoefficient 20 82 3 1) v1811_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1811_mg : Scalar.QComplex := ((-93086222014640989175626 : Int)/10^30,(193025850476848571450 : Int)/10^30)
theorem v1811_mg_checked : Scalar.distance (sourceCoefficient 20 82 3 2) v1811_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1811_upper : Scalar.QComplex := ((999995688262678781688757456489 : Int)/10^30,(-2936572160080166546668836121 : Int)/10^30)
theorem v1811_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 82 5) 1) 14) v1811_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1811 : Material (20 : Basis) (82 : Basis) where
  plus := ![v1811_pa,v1811_pb,v1811_pg]
  minus := ![(Primitive.Addresses.material1811 1).one,v1811_mb,v1811_mg]
  upper := v1811_upper
  lower := (Primitive.Addresses.material1811 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1811_pa_checked.trans (by decide +kernel)
    · exact v1811_pb_checked.trans (by decide +kernel)
    · exact v1811_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 82 Primitive.Addresses.material1811
    · exact v1811_mb_checked.trans (by decide +kernel)
    · exact v1811_mg_checked.trans (by decide +kernel)
  upper_error := v1811_upper_checked
  lower_error := reuse_lower_error 20 82 Primitive.Addresses.material1811

def v1812_pa : Scalar.QComplex := ((999999250624592567281774966739 : Int)/10^30,(-1224234558122721507547502345 : Int)/10^30)
theorem v1812_pa_checked : Scalar.distance (sourceCoefficient 20 83 1 0) v1812_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1812_pb : Scalar.QComplex := ((-528229601889810208097636 : Int)/10^30,(-431477123842623588794607154 : Int)/10^30)
theorem v1812_pb_checked : Scalar.distance (sourceCoefficient 20 83 1 1) v1812_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1812_pg : Scalar.QComplex := ((-93086352177442870166437 : Int)/10^30,(113959614623740446741 : Int)/10^30)
theorem v1812_pg_checked : Scalar.distance (sourceCoefficient 20 83 1 2) v1812_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1812_mb : Scalar.QComplex := ((-900574730073701600582656 : Int)/10^30,(-431476507345615050679358412 : Int)/10^30)
theorem v1812_mb_checked : Scalar.distance (sourceCoefficient 20 83 3 1) v1812_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1812_mg : Scalar.QComplex := ((-93086219175124828270831 : Int)/10^30,(194288901666830031341 : Int)/10^30)
theorem v1812_mg_checked : Scalar.distance (sourceCoefficient 20 83 3 2) v1812_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1812_upper : Scalar.QComplex := ((999995648325391297347196441616 : Int)/10^30,(-2950140722123845667812696055 : Int)/10^30)
theorem v1812_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 83 5) 1) 14) v1812_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1812 : Material (20 : Basis) (83 : Basis) where
  plus := ![v1812_pa,v1812_pb,v1812_pg]
  minus := ![(Primitive.Addresses.material1812 1).one,v1812_mb,v1812_mg]
  upper := v1812_upper
  lower := (Primitive.Addresses.material1812 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1812_pa_checked.trans (by decide +kernel)
    · exact v1812_pb_checked.trans (by decide +kernel)
    · exact v1812_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 83 Primitive.Addresses.material1812
    · exact v1812_mb_checked.trans (by decide +kernel)
    · exact v1812_mg_checked.trans (by decide +kernel)
  upper_error := v1812_upper_checked
  lower_error := reuse_lower_error 20 83 Primitive.Addresses.material1812

def v1813_pa : Scalar.QComplex := ((999999206988768221310846023457 : Int)/10^30,(-1259373588213824889566253931 : Int)/10^30)
theorem v1813_pa_checked : Scalar.distance (sourceCoefficient 20 84 1 0) v1813_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1813_pb : Scalar.QComplex := ((-543391294329546515125862 : Int)/10^30,(-431477099805499746449879212 : Int)/10^30)
theorem v1813_pb_checked : Scalar.distance (sourceCoefficient 20 84 1 1) v1813_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1813_pg : Scalar.QComplex := ((-93086347553621530951900 : Int)/10^30,(117230580497490590261 : Int)/10^30)
theorem v1813_pg_checked : Scalar.distance (sourceCoefficient 20 84 1 2) v1813_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1813_mb : Scalar.QComplex := ((-915736396125091604648099 : Int)/10^30,(-431476470224642440240586845 : Int)/10^30)
theorem v1813_mb_checked : Scalar.distance (sourceCoefficient 20 84 3 1) v1813_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1813_mg : Scalar.QComplex := ((-93086211728608980504146 : Int)/10^30,(197559862332500522978 : Int)/10^30)
theorem v1813_mg_checked : Scalar.distance (sourceCoefficient 20 84 3 2) v1813_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1813_upper : Scalar.QComplex := ((999995544042853792474601781733 : Int)/10^30,(-2985279624568017239479877263 : Int)/10^30)
theorem v1813_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 84 5) 1) 14) v1813_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1813 : Material (20 : Basis) (84 : Basis) where
  plus := ![v1813_pa,v1813_pb,v1813_pg]
  minus := ![(Primitive.Addresses.material1813 1).one,v1813_mb,v1813_mg]
  upper := v1813_upper
  lower := (Primitive.Addresses.material1813 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1813_pa_checked.trans (by decide +kernel)
    · exact v1813_pb_checked.trans (by decide +kernel)
    · exact v1813_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 84 Primitive.Addresses.material1813
    · exact v1813_mb_checked.trans (by decide +kernel)
    · exact v1813_mg_checked.trans (by decide +kernel)
  upper_error := v1813_upper_checked
  lower_error := reuse_lower_error 20 84 Primitive.Addresses.material1813

def v1814_pa : Scalar.QComplex := ((999999104301712753096038576324 : Int)/10^30,(-1338430338948720239226227661 : Int)/10^30)
theorem v1814_pa_checked : Scalar.distance (sourceCoefficient 20 85 1 0) v1814_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1814_pb : Scalar.QComplex := ((-577502482352008741332728 : Int)/10^30,(-431477043129213209918247255 : Int)/10^30)
theorem v1814_pb_checked : Scalar.distance (sourceCoefficient 20 85 1 1) v1814_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1814_pg : Scalar.QComplex := ((-93086336660599607462182 : Int)/10^30,(124589688722911813221 : Int)/10^30)
theorem v1814_pg_checked : Scalar.distance (sourceCoefficient 20 85 1 2) v1814_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1814_mb : Scalar.QComplex := ((-949847522537316895947197 : Int)/10^30,(-431476384111958054373756641 : Int)/10^30)
theorem v1814_mb_checked : Scalar.distance (sourceCoefficient 20 85 3 1) v1814_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1814_mg : Scalar.QComplex := ((-93086194485012156376579 : Int)/10^30,(204918958417602109277 : Int)/10^30)
theorem v1814_mg_checked : Scalar.distance (sourceCoefficient 20 85 3 2) v1814_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1814_upper : Scalar.QComplex := ((999995304911171468539367676815 : Int)/10^30,(-3064336080328626986569801454 : Int)/10^30)
theorem v1814_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 85 5) 1) 14) v1814_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1814 : Material (20 : Basis) (85 : Basis) where
  plus := ![v1814_pa,v1814_pb,v1814_pg]
  minus := ![(Primitive.Addresses.material1814 1).one,v1814_mb,v1814_mg]
  upper := v1814_upper
  lower := (Primitive.Addresses.material1814 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1814_pa_checked.trans (by decide +kernel)
    · exact v1814_pb_checked.trans (by decide +kernel)
    · exact v1814_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 85 Primitive.Addresses.material1814
    · exact v1814_mb_checked.trans (by decide +kernel)
    · exact v1814_mg_checked.trans (by decide +kernel)
  upper_error := v1814_upper_checked
  lower_error := reuse_lower_error 20 85 Primitive.Addresses.material1814

def v1815_pa : Scalar.QComplex := ((999999084674826780267111467102 : Int)/10^30,(-1353014969843014356044831759 : Int)/10^30)
theorem v1815_pa_checked : Scalar.distance (sourceCoefficient 20 86 1 0) v1815_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1815_pb : Scalar.QComplex := ((-583795418181657226058041 : Int)/10^30,(-431477032280545021472059260 : Int)/10^30)
theorem v1815_pb_checked : Scalar.distance (sourceCoefficient 20 86 1 1) v1815_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1815_pg : Scalar.QComplex := ((-93086334576862057736738 : Int)/10^30,(125947319453061756501 : Int)/10^30)
theorem v1815_pg_checked : Scalar.distance (sourceCoefficient 20 86 1 2) v1815_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1815_mb : Scalar.QComplex := ((-956140446661905729167412 : Int)/10^30,(-431476367832773707704501117 : Int)/10^30)
theorem v1815_mb_checked : Scalar.distance (sourceCoefficient 20 86 3 1) v1815_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1815_mg : Scalar.QComplex := ((-93086191229701207820718 : Int)/10^30,(206276586844072427575 : Int)/10^30)
theorem v1815_mg_checked : Scalar.distance (sourceCoefficient 20 86 3 2) v1815_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1815_upper : Scalar.QComplex := ((999995260112564911479098200260 : Int)/10^30,(-3078920655626601965514016289 : Int)/10^30)
theorem v1815_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 86 5) 1) 14) v1815_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1815 : Material (20 : Basis) (86 : Basis) where
  plus := ![v1815_pa,v1815_pb,v1815_pg]
  minus := ![(Primitive.Addresses.material1815 1).one,v1815_mb,v1815_mg]
  upper := v1815_upper
  lower := (Primitive.Addresses.material1815 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1815_pa_checked.trans (by decide +kernel)
    · exact v1815_pb_checked.trans (by decide +kernel)
    · exact v1815_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 86 Primitive.Addresses.material1815
    · exact v1815_mb_checked.trans (by decide +kernel)
    · exact v1815_mg_checked.trans (by decide +kernel)
  upper_error := v1815_upper_checked
  lower_error := reuse_lower_error 20 86 Primitive.Addresses.material1815

def v1816_pa : Scalar.QComplex := ((999999083367677516838299083226 : Int)/10^30,(-1353980725398817773347381097 : Int)/10^30)
theorem v1816_pa_checked : Scalar.distance (sourceCoefficient 20 87 1 0) v1816_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1816_pb : Scalar.QComplex := ((-584212119689345301977948 : Int)/10^30,(-431477031557855079027127134 : Int)/10^30)
theorem v1816_pb_checked : Scalar.distance (sourceCoefficient 20 87 1 1) v1816_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1816_pg : Scalar.QComplex := ((-93086334438067008180977 : Int)/10^30,(126037218156958918495 : Int)/10^30)
theorem v1816_pg_checked : Scalar.distance (sourceCoefficient 20 87 1 2) v1816_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1816_mb : Scalar.QComplex := ((-956557147390787917992110 : Int)/10^30,(-431476366750489400754476073 : Int)/10^30)
theorem v1816_mb_checked : Scalar.distance (sourceCoefficient 20 87 3 1) v1816_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1816_mg : Scalar.QComplex := ((-93086191013327677368768 : Int)/10^30,(206366485394722316865 : Int)/10^30)
theorem v1816_mg_checked : Scalar.distance (sourceCoefficient 20 87 3 2) v1816_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1816_upper : Scalar.QComplex := ((999995257138611118238496838071 : Int)/10^30,(-3079886407488004883040803561 : Int)/10^30)
theorem v1816_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 87 5) 1) 14) v1816_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1816 : Material (20 : Basis) (87 : Basis) where
  plus := ![v1816_pa,v1816_pb,v1816_pg]
  minus := ![(Primitive.Addresses.material1816 1).one,v1816_mb,v1816_mg]
  upper := v1816_upper
  lower := (Primitive.Addresses.material1816 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1816_pa_checked.trans (by decide +kernel)
    · exact v1816_pb_checked.trans (by decide +kernel)
    · exact v1816_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 87 Primitive.Addresses.material1816
    · exact v1816_mb_checked.trans (by decide +kernel)
    · exact v1816_mg_checked.trans (by decide +kernel)
  upper_error := v1816_upper_checked
  lower_error := reuse_lower_error 20 87 Primitive.Addresses.material1816

def v1817_pa : Scalar.QComplex := ((999999067376270547697199182696 : Int)/10^30,(-1365740308081146466428350006 : Int)/10^30)
theorem v1817_pa_checked : Scalar.distance (sourceCoefficient 20 88 1 0) v1817_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1817_pb : Scalar.QComplex := ((-589286111514835866924809 : Int)/10^30,(-431477022714930367109472635 : Int)/10^30)
theorem v1817_pb_checked : Scalar.distance (sourceCoefficient 20 88 1 1) v1817_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1817_pg : Scalar.QComplex := ((-93086332739894656348101 : Int)/10^30,(127131875320531532522 : Int)/10^30)
theorem v1817_pg_checked : Scalar.distance (sourceCoefficient 20 88 1 2) v1817_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1817_mb : Scalar.QComplex := ((-961631129695953677586260 : Int)/10^30,(-431476353528941560172082323 : Int)/10^30)
theorem v1817_mb_checked : Scalar.distance (sourceCoefficient 20 88 3 1) v1817_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1817_mg : Scalar.QComplex := ((-93086188370516127208391 : Int)/10^30,(207461140685257783802 : Int)/10^30)
theorem v1817_mg_checked : Scalar.distance (sourceCoefficient 20 88 3 2) v1817_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1817_upper : Scalar.QComplex := ((999995220851255077727663077669 : Int)/10^30,(-3091645945056098848781763800 : Int)/10^30)
theorem v1817_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 88 5) 1) 14) v1817_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1817 : Material (20 : Basis) (88 : Basis) where
  plus := ![v1817_pa,v1817_pb,v1817_pg]
  minus := ![(Primitive.Addresses.material1817 1).one,v1817_mb,v1817_mg]
  upper := v1817_upper
  lower := (Primitive.Addresses.material1817 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1817_pa_checked.trans (by decide +kernel)
    · exact v1817_pb_checked.trans (by decide +kernel)
    · exact v1817_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 88 Primitive.Addresses.material1817
    · exact v1817_mb_checked.trans (by decide +kernel)
    · exact v1817_mg_checked.trans (by decide +kernel)
  upper_error := v1817_upper_checked
  lower_error := reuse_lower_error 20 88 Primitive.Addresses.material1817

def v1818_pa : Scalar.QComplex := ((999999045272777357877143899642 : Int)/10^30,(-1381829777425633586950097374 : Int)/10^30)
theorem v1818_pa_checked : Scalar.distance (sourceCoefficient 20 89 1 0) v1818_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1818_pb : Scalar.QComplex := ((-596228350601165683636410 : Int)/10^30,(-431477010487144355430595000 : Int)/10^30)
theorem v1818_pb_checked : Scalar.distance (sourceCoefficient 20 89 1 1) v1818_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1818_pg : Scalar.QComplex := ((-93086330392123251021675 : Int)/10^30,(128629586013284067285 : Int)/10^30)
theorem v1818_pg_checked : Scalar.distance (sourceCoefficient 20 89 1 2) v1818_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1818_mb : Scalar.QComplex := ((-968573355645341997416715 : Int)/10^30,(-431476335310320436795851993 : Int)/10^30)
theorem v1818_mb_checked : Scalar.distance (sourceCoefficient 20 89 3 1) v1818_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1818_mg : Scalar.QComplex := ((-93086184730288722604697 : Int)/10^30,(208958848794323195796 : Int)/10^30)
theorem v1818_mg_checked : Scalar.distance (sourceCoefficient 20 89 3 2) v1818_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1818_upper : Scalar.QComplex := ((999995170978830345136450395456 : Int)/10^30,(-3107735352288587350133435113 : Int)/10^30)
theorem v1818_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 89 5) 1) 14) v1818_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1818 : Material (20 : Basis) (89 : Basis) where
  plus := ![v1818_pa,v1818_pb,v1818_pg]
  minus := ![(Primitive.Addresses.material1818 1).one,v1818_mb,v1818_mg]
  upper := v1818_upper
  lower := (Primitive.Addresses.material1818 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1818_pa_checked.trans (by decide +kernel)
    · exact v1818_pb_checked.trans (by decide +kernel)
    · exact v1818_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 89 Primitive.Addresses.material1818
    · exact v1818_mb_checked.trans (by decide +kernel)
    · exact v1818_mg_checked.trans (by decide +kernel)
  upper_error := v1818_upper_checked
  lower_error := reuse_lower_error 20 89 Primitive.Addresses.material1818

def v1819_pa : Scalar.QComplex := ((999999008721475541802591786533 : Int)/10^30,(-1408032693613071530090530493 : Int)/10^30)
theorem v1819_pa_checked : Scalar.distance (sourceCoefficient 20 90 1 0) v1819_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1819_pb : Scalar.QComplex := ((-607534311055819630139278 : Int)/10^30,(-431476990254499687518749945 : Int)/10^30)
theorem v1819_pb_checked : Scalar.distance (sourceCoefficient 20 90 1 1) v1819_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1819_pg : Scalar.QComplex := ((-93086326508425193213204 : Int)/10^30,(131068720977812122121 : Int)/10^30)
theorem v1819_pg_checked : Scalar.distance (sourceCoefficient 20 90 1 2) v1819_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1819_mb : Scalar.QComplex := ((-979879294430409054814187 : Int)/10^30,(-431476305321148631612365833 : Int)/10^30)
theorem v1819_mb_checked : Scalar.distance (sourceCoefficient 20 90 3 1) v1819_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1819_mg : Scalar.QComplex := ((-93086178741728491047605 : Int)/10^30,(211397979499193320741 : Int)/10^30)
theorem v1819_mg_checked : Scalar.distance (sourceCoefficient 20 90 3 2) v1819_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1819_upper : Scalar.QComplex := ((999995089203726738402006125770 : Int)/10^30,(-3133938166365628616492514943 : Int)/10^30)
theorem v1819_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 90 5) 1) 14) v1819_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1819 : Material (20 : Basis) (90 : Basis) where
  plus := ![v1819_pa,v1819_pb,v1819_pg]
  minus := ![(Primitive.Addresses.material1819 1).one,v1819_mb,v1819_mg]
  upper := v1819_upper
  lower := (Primitive.Addresses.material1819 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1819_pa_checked.trans (by decide +kernel)
    · exact v1819_pb_checked.trans (by decide +kernel)
    · exact v1819_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 90 Primitive.Addresses.material1819
    · exact v1819_mb_checked.trans (by decide +kernel)
    · exact v1819_mg_checked.trans (by decide +kernel)
  upper_error := v1819_upper_checked
  lower_error := reuse_lower_error 20 90 Primitive.Addresses.material1819

def v1820_pa : Scalar.QComplex := ((999998987828460498529901542567 : Int)/10^30,(-1422793749814678803622969699 : Int)/10^30)
theorem v1820_pa_checked : Scalar.distance (sourceCoefficient 20 91 1 0) v1820_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1820_pb : Scalar.QComplex := ((-613903369834299180492139 : Int)/10^30,(-431476978682779608827926058 : Int)/10^30)
theorem v1820_pb_checked : Scalar.distance (sourceCoefficient 20 91 1 1) v1820_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1820_pg : Scalar.QComplex := ((-93086324287762760950649 : Int)/10^30,(132442774444658094276 : Int)/10^30)
theorem v1820_pg_checked : Scalar.distance (sourceCoefficient 20 91 1 2) v1820_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1820_mb : Scalar.QComplex := ((-986248340851523684588662 : Int)/10^30,(-431476288253221987532873915 : Int)/10^30)
theorem v1820_mb_checked : Scalar.distance (sourceCoefficient 20 91 3 1) v1820_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1820_mg : Scalar.QComplex := ((-93086175335320628821954 : Int)/10^30,(212772030538084725724 : Int)/10^30)
theorem v1820_mg_checked : Scalar.distance (sourceCoefficient 20 91 3 2) v1820_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1820_upper : Scalar.QComplex := ((999995042834498921404839337628 : Int)/10^30,(-3148699164522928068026102913 : Int)/10^30)
theorem v1820_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 91 5) 1) 14) v1820_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1820 : Material (20 : Basis) (91 : Basis) where
  plus := ![v1820_pa,v1820_pb,v1820_pg]
  minus := ![(Primitive.Addresses.material1820 1).one,v1820_mb,v1820_mg]
  upper := v1820_upper
  lower := (Primitive.Addresses.material1820 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1820_pa_checked.trans (by decide +kernel)
    · exact v1820_pb_checked.trans (by decide +kernel)
    · exact v1820_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 91 Primitive.Addresses.material1820
    · exact v1820_mb_checked.trans (by decide +kernel)
    · exact v1820_mg_checked.trans (by decide +kernel)
  upper_error := v1820_upper_checked
  lower_error := reuse_lower_error 20 91 Primitive.Addresses.material1820

def v1821_pa : Scalar.QComplex := ((999998941850918762768831277306 : Int)/10^30,(-1454749821376508784291914886 : Int)/10^30)
theorem v1821_pa_checked : Scalar.distance (sourceCoefficient 20 92 1 0) v1821_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1821_pb : Scalar.QComplex := ((-627691684789832166858583 : Int)/10^30,(-431476953201836993488079810 : Int)/10^30)
theorem v1821_pb_checked : Scalar.distance (sourceCoefficient 20 92 1 1) v1821_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1821_pg : Scalar.QComplex := ((-93086319399206512183838 : Int)/10^30,(135417449810442418501 : Int)/10^30)
theorem v1821_pg_checked : Scalar.distance (sourceCoefficient 20 92 1 2) v1821_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1821_mb : Scalar.QComplex := ((-1000036628684130997901799 : Int)/10^30,(-431476250873594055940427859 : Int)/10^30)
theorem v1821_mb_checked : Scalar.distance (sourceCoefficient 20 92 3 1) v1821_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1821_mg : Scalar.QComplex := ((-93086167879755334021292 : Int)/10^30,(215746700577657591603 : Int)/10^30)
theorem v1821_mg_checked : Scalar.distance (sourceCoefficient 20 92 3 2) v1821_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1821_upper : Scalar.QComplex := ((999994941703745180238829119151 : Int)/10^30,(-3180655109136877295286894696 : Int)/10^30)
theorem v1821_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 92 5) 1) 14) v1821_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1821 : Material (20 : Basis) (92 : Basis) where
  plus := ![v1821_pa,v1821_pb,v1821_pg]
  minus := ![(Primitive.Addresses.material1821 1).one,v1821_mb,v1821_mg]
  upper := v1821_upper
  lower := (Primitive.Addresses.material1821 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1821_pa_checked.trans (by decide +kernel)
    · exact v1821_pb_checked.trans (by decide +kernel)
    · exact v1821_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 92 Primitive.Addresses.material1821
    · exact v1821_mb_checked.trans (by decide +kernel)
    · exact v1821_mg_checked.trans (by decide +kernel)
  upper_error := v1821_upper_checked
  lower_error := reuse_lower_error 20 92 Primitive.Addresses.material1821

def v1822_pa : Scalar.QComplex := ((999998885959466679505677716634 : Int)/10^30,(-1492675391890239062621079037 : Int)/10^30)
theorem v1822_pa_checked : Scalar.distance (sourceCoefficient 20 93 1 0) v1822_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1822_pb : Scalar.QComplex := ((-644055701438555109310232 : Int)/10^30,(-431476922198605724743619275 : Int)/10^30)
theorem v1822_pb_checked : Scalar.distance (sourceCoefficient 20 93 1 1) v1822_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1822_pg : Scalar.QComplex := ((-93086313453539113148440 : Int)/10^30,(138947804207365031369 : Int)/10^30)
theorem v1822_pg_checked : Scalar.distance (sourceCoefficient 20 93 1 2) v1822_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1822_mb : Scalar.QComplex := ((-1016400612485390418302930 : Int)/10^30,(-431476205748964971218824331 : Int)/10^30)
theorem v1822_mb_checked : Scalar.distance (sourceCoefficient 20 93 3 1) v1822_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1822_mg : Scalar.QComplex := ((-93086158887553305545015 : Int)/10^30,(219277048529224734881 : Int)/10^30)
theorem v1822_mg_checked : Scalar.distance (sourceCoefficient 20 93 3 2) v1822_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1822_upper : Scalar.QComplex := ((999994820356282214910284723488 : Int)/10^30,(-3218580526701349481090320477 : Int)/10^30)
theorem v1822_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 93 5) 1) 14) v1822_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1822 : Material (20 : Basis) (93 : Basis) where
  plus := ![v1822_pa,v1822_pb,v1822_pg]
  minus := ![(Primitive.Addresses.material1822 1).one,v1822_mb,v1822_mg]
  upper := v1822_upper
  lower := (Primitive.Addresses.material1822 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1822_pa_checked.trans (by decide +kernel)
    · exact v1822_pb_checked.trans (by decide +kernel)
    · exact v1822_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 93 Primitive.Addresses.material1822
    · exact v1822_mb_checked.trans (by decide +kernel)
    · exact v1822_mg_checked.trans (by decide +kernel)
  upper_error := v1822_upper_checked
  lower_error := reuse_lower_error 20 93 Primitive.Addresses.material1822

def v1823_pa : Scalar.QComplex := ((999998818086308075336957941871 : Int)/10^30,(-1537473897966840582137758705 : Int)/10^30)
theorem v1823_pa_checked : Scalar.distance (sourceCoefficient 20 94 1 0) v1823_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1823_pb : Scalar.QComplex := ((-663385231575653053826591 : Int)/10^30,(-431476884510902022650359717 : Int)/10^30)
theorem v1823_pb_checked : Scalar.distance (sourceCoefficient 20 94 1 1) v1823_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1823_pg : Scalar.QComplex := ((-93086306229154629441026 : Int)/10^30,(143117935238520580041 : Int)/10^30)
theorem v1823_pg_checked : Scalar.distance (sourceCoefficient 20 94 1 2) v1823_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1823_mb : Scalar.QComplex := ((-1035730102902429985867594 : Int)/10^30,(-431476151380761363384847890 : Int)/10^30)
theorem v1823_mb_checked : Scalar.distance (sourceCoefficient 20 94 3 1) v1823_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1823_mg : Scalar.QComplex := ((-93086148064536247648473 : Int)/10^30,(223447171773331481009 : Int)/10^30)
theorem v1823_mg_checked : Scalar.distance (sourceCoefficient 20 94 3 2) v1823_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1823_upper : Scalar.QComplex := ((999994675165067300348492289080 : Int)/10^30,(-3263378848912924255750738866 : Int)/10^30)
theorem v1823_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 94 5) 1) 14) v1823_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1823 : Material (20 : Basis) (94 : Basis) where
  plus := ![v1823_pa,v1823_pb,v1823_pg]
  minus := ![(Primitive.Addresses.material1823 1).one,v1823_mb,v1823_mg]
  upper := v1823_upper
  lower := (Primitive.Addresses.material1823 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1823_pa_checked.trans (by decide +kernel)
    · exact v1823_pb_checked.trans (by decide +kernel)
    · exact v1823_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 94 Primitive.Addresses.material1823
    · exact v1823_mb_checked.trans (by decide +kernel)
    · exact v1823_mg_checked.trans (by decide +kernel)
  upper_error := v1823_upper_checked
  lower_error := reuse_lower_error 20 94 Primitive.Addresses.material1823

def v1824_pa : Scalar.QComplex := ((999998749035742563665279842982 : Int)/10^30,(-1581748067791168840242293911 : Int)/10^30)
theorem v1824_pa_checked : Scalar.distance (sourceCoefficient 20 95 1 0) v1824_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1824_pb : Scalar.QComplex := ((-682488521431369291108797 : Int)/10^30,(-431476846129916486852194055 : Int)/10^30)
theorem v1824_pb_checked : Scalar.distance (sourceCoefficient 20 95 1 1) v1824_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1824_pg : Scalar.QComplex := ((-93086298875185953140471 : Int)/10^30,(147239257574705152187 : Int)/10^30)
theorem v1824_pg_checked : Scalar.distance (sourceCoefficient 20 95 1 2) v1824_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1824_mb : Scalar.QComplex := ((-1054833352524056444415524 : Int)/10^30,(-431476096514511353334867915 : Int)/10^30)
theorem v1824_mb_checked : Scalar.distance (sourceCoefficient 20 95 3 1) v1824_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1824_mg : Scalar.QComplex := ((-93086137154054750906840 : Int)/10^30,(227568486228815636466 : Int)/10^30)
theorem v1824_mg_checked : Scalar.distance (sourceCoefficient 20 95 3 2) v1824_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1824_upper : Scalar.QComplex := ((999994529701404035903441532978 : Int)/10^30,(-3307652833621065515067342186 : Int)/10^30)
theorem v1824_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 95 5) 1) 14) v1824_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1824 : Material (20 : Basis) (95 : Basis) where
  plus := ![v1824_pa,v1824_pb,v1824_pg]
  minus := ![(Primitive.Addresses.material1824 1).one,v1824_mb,v1824_mg]
  upper := v1824_upper
  lower := (Primitive.Addresses.material1824 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1824_pa_checked.trans (by decide +kernel)
    · exact v1824_pb_checked.trans (by decide +kernel)
    · exact v1824_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 95 Primitive.Addresses.material1824
    · exact v1824_mb_checked.trans (by decide +kernel)
    · exact v1824_mg_checked.trans (by decide +kernel)
  upper_error := v1824_upper_checked
  lower_error := reuse_lower_error 20 95 Primitive.Addresses.material1824

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
