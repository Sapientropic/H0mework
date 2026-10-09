import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B070
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B071

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1697_pa : Scalar.QComplex := ((999999815086817040493713886938 : Int)/10^30,(-608133481832835232695125781 : Int)/10^30)
theorem v1697_pa_checked : Scalar.distance (sourceCoefficient 19 45 1 0) v1697_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1697_pb : Scalar.QComplex := ((-262395920087475129093970 : Int)/10^30,(-431477429554089531678516300 : Int)/10^30)
theorem v1697_pb_checked : Scalar.distance (sourceCoefficient 19 45 1 1) v1697_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1697_pg : Scalar.QComplex := ((-93086411426237486022624 : Int)/10^30,(56608973959707179190 : Int)/10^30)
theorem v1697_pg_checked : Scalar.distance (sourceCoefficient 19 45 1 2) v1697_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1697_mb : Scalar.QComplex := ((-634741411068621831431487 : Int)/10^30,(-431477042459461854047274301 : Int)/10^30)
theorem v1697_mb_checked : Scalar.distance (sourceCoefficient 19 45 3 1) v1697_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1697_mg : Scalar.QComplex := ((-93086327914917299182793 : Int)/10^30,(136938333486102623603 : Int)/10^30)
theorem v1697_mg_checked : Scalar.distance (sourceCoefficient 19 45 3 2) v1697_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1697_upper : Scalar.QComplex := ((999997276121340493691185536108 : Int)/10^30,(-2334041537654732038218495570 : Int)/10^30)
theorem v1697_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 45 5) 1) 14) v1697_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1697 : Material (19 : Basis) (45 : Basis) where
  plus := ![v1697_pa,v1697_pb,v1697_pg]
  minus := ![(Primitive.Addresses.material1697 1).one,v1697_mb,v1697_mg]
  upper := v1697_upper
  lower := (Primitive.Addresses.material1697 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1697_pa_checked.trans (by decide +kernel)
    · exact v1697_pb_checked.trans (by decide +kernel)
    · exact v1697_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 45 Primitive.Addresses.material1697
    · exact v1697_mb_checked.trans (by decide +kernel)
    · exact v1697_mg_checked.trans (by decide +kernel)
  upper_error := v1697_upper_checked
  lower_error := reuse_lower_error 19 45 Primitive.Addresses.material1697

def v1698_pa : Scalar.QComplex := ((999999805001278620230282339258 : Int)/10^30,(-624497721961448067199626236 : Int)/10^30)
theorem v1698_pa_checked : Scalar.distance (sourceCoefficient 19 46 1 0) v1698_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1698_pb : Scalar.QComplex := ((-269456721056519503307262 : Int)/10^30,(-431477424235404526847399905 : Int)/10^30)
theorem v1698_pb_checked : Scalar.distance (sourceCoefficient 19 46 1 1) v1698_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1698_pg : Scalar.QComplex := ((-93086410383100821920985 : Int)/10^30,(58132262565531820740 : Int)/10^30)
theorem v1698_pg_checked : Scalar.distance (sourceCoefficient 19 46 1 2) v1698_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1698_mb : Scalar.QComplex := ((-641802204818821695834887 : Int)/10^30,(-431477031047625599991049417 : Int)/10^30)
theorem v1698_mb_checked : Scalar.distance (sourceCoefficient 19 46 3 1) v1698_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1698_mg : Scalar.QComplex := ((-93086325557251563033960 : Int)/10^30,(138461620624557339488 : Int)/10^30)
theorem v1698_mg_checked : Scalar.distance (sourceCoefficient 19 46 3 2) v1698_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1698_upper : Scalar.QComplex := ((999997237792623184934529898314 : Int)/10^30,(-2350405736004007119355981788 : Int)/10^30)
theorem v1698_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 46 5) 1) 14) v1698_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1698 : Material (19 : Basis) (46 : Basis) where
  plus := ![v1698_pa,v1698_pb,v1698_pg]
  minus := ![(Primitive.Addresses.material1698 1).one,v1698_mb,v1698_mg]
  upper := v1698_upper
  lower := (Primitive.Addresses.material1698 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1698_pa_checked.trans (by decide +kernel)
    · exact v1698_pb_checked.trans (by decide +kernel)
    · exact v1698_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 46 Primitive.Addresses.material1698
    · exact v1698_mb_checked.trans (by decide +kernel)
    · exact v1698_mg_checked.trans (by decide +kernel)
  upper_error := v1698_upper_checked
  lower_error := reuse_lower_error 19 46 Primitive.Addresses.material1698

def v1699_pa : Scalar.QComplex := ((999999802534225834248513218846 : Int)/10^30,(-628435763892198457590583298 : Int)/10^30)
theorem v1699_pa_checked : Scalar.distance (sourceCoefficient 19 47 1 0) v1699_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1699_pb : Scalar.QComplex := ((-271155897426812494454811 : Int)/10^30,(-431477422932468912076653733 : Int)/10^30)
theorem v1699_pb_checked : Scalar.distance (sourceCoefficient 19 47 1 1) v1699_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1699_pg : Scalar.QComplex := ((-93086410127729390088540 : Int)/10^30,(58498840808120986231 : Int)/10^30)
theorem v1699_pg_checked : Scalar.distance (sourceCoefficient 19 47 1 2) v1699_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1699_mb : Scalar.QComplex := ((-643501379432058914620495 : Int)/10^30,(-431477028278377790862791131 : Int)/10^30)
theorem v1699_mb_checked : Scalar.distance (sourceCoefficient 19 47 3 1) v1699_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1699_mg : Scalar.QComplex := ((-93086324985539713004684 : Int)/10^30,(138828198510278627641 : Int)/10^30)
theorem v1699_mg_checked : Scalar.distance (sourceCoefficient 19 47 3 2) v1699_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1699_upper : Scalar.QComplex := ((999997228528870957236135344110 : Int)/10^30,(-2354343767811597349470846334 : Int)/10^30)
theorem v1699_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 47 5) 1) 14) v1699_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1699 : Material (19 : Basis) (47 : Basis) where
  plus := ![v1699_pa,v1699_pb,v1699_pg]
  minus := ![(Primitive.Addresses.material1699 1).one,v1699_mb,v1699_mg]
  upper := v1699_upper
  lower := (Primitive.Addresses.material1699 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1699_pa_checked.trans (by decide +kernel)
    · exact v1699_pb_checked.trans (by decide +kernel)
    · exact v1699_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 47 Primitive.Addresses.material1699
    · exact v1699_mb_checked.trans (by decide +kernel)
    · exact v1699_mg_checked.trans (by decide +kernel)
  upper_error := v1699_upper_checked
  lower_error := reuse_lower_error 19 47 Primitive.Addresses.material1699

def v1700_pa : Scalar.QComplex := ((999999784919658041216476022668 : Int)/10^30,(-655866326058910841874764262 : Int)/10^30)
theorem v1700_pa_checked : Scalar.distance (sourceCoefficient 19 48 1 0) v1700_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1700_pb : Scalar.QComplex := ((-282991566907265570143552 : Int)/10^30,(-431477413609315094782340158 : Int)/10^30)
theorem v1700_pb_checked : Scalar.distance (sourceCoefficient 19 48 1 1) v1700_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1700_pg : Scalar.QComplex := ((-93086408302207904563962 : Int)/10^30,(61052253750328408710 : Int)/10^30)
theorem v1700_pg_checked : Scalar.distance (sourceCoefficient 19 48 1 2) v1700_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1700_mb : Scalar.QComplex := ((-655337036460089480855011 : Int)/10^30,(-431477008741577742139056685 : Int)/10^30)
theorem v1700_mb_checked : Scalar.distance (sourceCoefficient 19 48 3 1) v1700_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1700_mg : Scalar.QComplex := ((-93086320956538539530042 : Int)/10^30,(141381608926390891427 : Int)/10^30)
theorem v1700_mg_checked : Scalar.distance (sourceCoefficient 19 48 3 2) v1700_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1700_upper : Scalar.QComplex := ((999997163571667580448914209054 : Int)/10^30,(-2381774258722563576951799536 : Int)/10^30)
theorem v1700_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 48 5) 1) 14) v1700_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1700 : Material (19 : Basis) (48 : Basis) where
  plus := ![v1700_pa,v1700_pb,v1700_pg]
  minus := ![(Primitive.Addresses.material1700 1).one,v1700_mb,v1700_mg]
  upper := v1700_upper
  lower := (Primitive.Addresses.material1700 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1700_pa_checked.trans (by decide +kernel)
    · exact v1700_pb_checked.trans (by decide +kernel)
    · exact v1700_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 48 Primitive.Addresses.material1700
    · exact v1700_mb_checked.trans (by decide +kernel)
    · exact v1700_mg_checked.trans (by decide +kernel)
  upper_error := v1700_upper_checked
  lower_error := reuse_lower_error 19 48 Primitive.Addresses.material1700

def v1701_pa : Scalar.QComplex := ((999999770222578919153538805079 : Int)/10^30,(-677904705223403567301770247 : Int)/10^30)
theorem v1701_pa_checked : Scalar.distance (sourceCoefficient 19 49 1 0) v1701_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1701_pb : Scalar.QComplex := ((-292500630803017474605553 : Int)/10^30,(-431477405805264727437447000 : Int)/10^30)
theorem v1701_pb_checked : Scalar.distance (sourceCoefficient 19 49 1 1) v1701_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1701_pg : Scalar.QComplex := ((-93086406776340476471624 : Int)/10^30,(63103727645832726071 : Int)/10^30)
theorem v1701_pg_checked : Scalar.distance (sourceCoefficient 19 49 1 2) v1701_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1701_mb : Scalar.QComplex := ((-664846090080638325601874 : Int)/10^30,(-431476992731636410904532575 : Int)/10^30)
theorem v1701_mb_checked : Scalar.distance (sourceCoefficient 19 49 3 1) v1701_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1701_mg : Scalar.QComplex := ((-93086317660342102722049 : Int)/10^30,(143433080741282852577 : Int)/10^30)
theorem v1701_mg_checked : Scalar.distance (sourceCoefficient 19 49 3 2) v1701_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1701_upper : Scalar.QComplex := ((999997110838367216184525316940 : Int)/10^30,(-2403812579697654090659615818 : Int)/10^30)
theorem v1701_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 49 5) 1) 14) v1701_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1701 : Material (19 : Basis) (49 : Basis) where
  plus := ![v1701_pa,v1701_pb,v1701_pg]
  minus := ![(Primitive.Addresses.material1701 1).one,v1701_mb,v1701_mg]
  upper := v1701_upper
  lower := (Primitive.Addresses.material1701 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1701_pa_checked.trans (by decide +kernel)
    · exact v1701_pb_checked.trans (by decide +kernel)
    · exact v1701_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 49 Primitive.Addresses.material1701
    · exact v1701_mb_checked.trans (by decide +kernel)
    · exact v1701_mg_checked.trans (by decide +kernel)
  upper_error := v1701_upper_checked
  lower_error := reuse_lower_error 19 49 Primitive.Addresses.material1701

def v1702_pa : Scalar.QComplex := ((999999768473467708426175947740 : Int)/10^30,(-680479985729641054476397913 : Int)/10^30)
theorem v1702_pa_checked : Scalar.distance (sourceCoefficient 19 50 1 0) v1702_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1702_pb : Scalar.QComplex := ((-293611806290989921966216 : Int)/10^30,(-431477404875094074768732712 : Int)/10^30)
theorem v1702_pb_checked : Scalar.distance (sourceCoefficient 19 50 1 1) v1702_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1702_pg : Scalar.QComplex := ((-93086406594594280956256 : Int)/10^30,(63343451296802703380 : Int)/10^30)
theorem v1702_pg_checked : Scalar.distance (sourceCoefficient 19 50 1 2) v1702_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1702_mb : Scalar.QComplex := ((-665957264352173975639794 : Int)/10^30,(-431476990842571703946843608 : Int)/10^30)
theorem v1702_mb_checked : Scalar.distance (sourceCoefficient 19 50 3 1) v1702_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1702_mg : Scalar.QComplex := ((-93086317271725260844451 : Int)/10^30,(143672804146153977533 : Int)/10^30)
theorem v1702_mg_checked : Scalar.distance (sourceCoefficient 19 50 3 2) v1702_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1702_upper : Scalar.QComplex := ((999997104644558084409469969312 : Int)/10^30,(-2406387853349506505906280667 : Int)/10^30)
theorem v1702_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 50 5) 1) 14) v1702_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1702 : Material (19 : Basis) (50 : Basis) where
  plus := ![v1702_pa,v1702_pb,v1702_pg]
  minus := ![(Primitive.Addresses.material1702 1).one,v1702_mb,v1702_mg]
  upper := v1702_upper
  lower := (Primitive.Addresses.material1702 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1702_pa_checked.trans (by decide +kernel)
    · exact v1702_pb_checked.trans (by decide +kernel)
    · exact v1702_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 50 Primitive.Addresses.material1702
    · exact v1702_mb_checked.trans (by decide +kernel)
    · exact v1702_mg_checked.trans (by decide +kernel)
  upper_error := v1702_upper_checked
  lower_error := reuse_lower_error 19 50 Primitive.Addresses.material1702

def v1703_pa : Scalar.QComplex := ((999999760720717365675494721584 : Int)/10^30,(-691779233581114309933462163 : Int)/10^30)
theorem v1703_pa_checked : Scalar.distance (sourceCoefficient 19 51 1 0) v1703_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1703_pb : Scalar.QComplex := ((-298487177019374294368356 : Int)/10^30,(-431477400748800751640690513 : Int)/10^30)
theorem v1703_pb_checked : Scalar.distance (sourceCoefficient 19 51 1 1) v1703_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1703_pg : Scalar.QComplex := ((-93086405788655631234344 : Int)/10^30,(64395257861747901352 : Int)/10^30)
theorem v1703_pg_checked : Scalar.distance (sourceCoefficient 19 51 1 2) v1703_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1703_mb : Scalar.QComplex := ((-670832629704429713907856 : Int)/10^30,(-431476982509054557177140787 : Int)/10^30)
theorem v1703_mb_checked : Scalar.distance (sourceCoefficient 19 51 3 1) v1703_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1703_mg : Scalar.QComplex := ((-93086315558125217271794 : Int)/10^30,(144724609623974764861 : Int)/10^30)
theorem v1703_mg_checked : Scalar.distance (sourceCoefficient 19 51 3 2) v1703_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1703_upper : Scalar.QComplex := ((999997077390342556584641578188 : Int)/10^30,(-2417687070991533621913860518 : Int)/10^30)
theorem v1703_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 51 5) 1) 14) v1703_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1703 : Material (19 : Basis) (51 : Basis) where
  plus := ![v1703_pa,v1703_pb,v1703_pg]
  minus := ![(Primitive.Addresses.material1703 1).one,v1703_mb,v1703_mg]
  upper := v1703_upper
  lower := (Primitive.Addresses.material1703 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1703_pa_checked.trans (by decide +kernel)
    · exact v1703_pb_checked.trans (by decide +kernel)
    · exact v1703_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 51 Primitive.Addresses.material1703
    · exact v1703_mb_checked.trans (by decide +kernel)
    · exact v1703_mg_checked.trans (by decide +kernel)
  upper_error := v1703_upper_checked
  lower_error := reuse_lower_error 19 51 Primitive.Addresses.material1703

def v1704_pa : Scalar.QComplex := ((999999743694764301275126167508 : Int)/10^30,(-715968159700608404846130259 : Int)/10^30)
theorem v1704_pa_checked : Scalar.distance (sourceCoefficient 19 52 1 0) v1704_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1704_pb : Scalar.QComplex := ((-308924153244185058052032 : Int)/10^30,(-431477391668489632746571777 : Int)/10^30)
theorem v1704_pb_checked : Scalar.distance (sourceCoefficient 19 52 1 1) v1704_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1704_pg : Scalar.QComplex := ((-93086404016725459784171 : Int)/10^30,(66646918458956393898 : Int)/10^30)
theorem v1704_pg_checked : Scalar.distance (sourceCoefficient 19 52 1 2) v1704_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1704_mb : Scalar.QComplex := ((-681269594207177702142847 : Int)/10^30,(-431476964422106401245724348 : Int)/10^30)
theorem v1704_mb_checked : Scalar.distance (sourceCoefficient 19 52 3 1) v1704_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1704_mg : Scalar.QComplex := ((-93086311843114021230020 : Int)/10^30,(146976267853691177904 : Int)/10^30)
theorem v1704_mg_checked : Scalar.distance (sourceCoefficient 19 52 3 2) v1704_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1704_upper : Scalar.QComplex := ((999997018616522770330376637805 : Int)/10^30,(-2441875931699213285943052325 : Int)/10^30)
theorem v1704_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 52 5) 1) 14) v1704_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1704 : Material (19 : Basis) (52 : Basis) where
  plus := ![v1704_pa,v1704_pb,v1704_pg]
  minus := ![(Primitive.Addresses.material1704 1).one,v1704_mb,v1704_mg]
  upper := v1704_upper
  lower := (Primitive.Addresses.material1704 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1704_pa_checked.trans (by decide +kernel)
    · exact v1704_pb_checked.trans (by decide +kernel)
    · exact v1704_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 52 Primitive.Addresses.material1704
    · exact v1704_mb_checked.trans (by decide +kernel)
    · exact v1704_mg_checked.trans (by decide +kernel)
  upper_error := v1704_upper_checked
  lower_error := reuse_lower_error 19 52 Primitive.Addresses.material1704

def v1705_pa : Scalar.QComplex := ((999999741036901289146866762235 : Int)/10^30,(-719670848624438707400957509 : Int)/10^30)
theorem v1705_pa_checked : Scalar.distance (sourceCoefficient 19 53 1 0) v1705_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1705_pb : Scalar.QComplex := ((-310521780016312859844588 : Int)/10^30,(-431477390248825676721899863 : Int)/10^30)
theorem v1705_pb_checked : Scalar.distance (sourceCoefficient 19 53 1 1) v1705_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1705_pg : Scalar.QComplex := ((-93086403739881692096048 : Int)/10^30,(66991588523227133936 : Int)/10^30)
theorem v1705_pg_checked : Scalar.distance (sourceCoefficient 19 53 1 2) v1705_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1705_mb : Scalar.QComplex := ((-682867219159329986763464 : Int)/10^30,(-431476961623763023919274479 : Int)/10^30)
theorem v1705_mb_checked : Scalar.distance (sourceCoefficient 19 53 3 1) v1705_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1705_mg : Scalar.QComplex := ((-93086311268835614521276 : Int)/10^30,(147320937550721797879 : Int)/10^30)
theorem v1705_mg_checked : Scalar.distance (sourceCoefficient 19 53 3 2) v1705_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1705_upper : Scalar.QComplex := ((999997009568158539560978627265 : Int)/10^30,(-2445578610521092945362658079 : Int)/10^30)
theorem v1705_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 53 5) 1) 14) v1705_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1705 : Material (19 : Basis) (53 : Basis) where
  plus := ![v1705_pa,v1705_pb,v1705_pg]
  minus := ![(Primitive.Addresses.material1705 1).one,v1705_mb,v1705_mg]
  upper := v1705_upper
  lower := (Primitive.Addresses.material1705 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1705_pa_checked.trans (by decide +kernel)
    · exact v1705_pb_checked.trans (by decide +kernel)
    · exact v1705_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 53 Primitive.Addresses.material1705
    · exact v1705_mb_checked.trans (by decide +kernel)
    · exact v1705_mg_checked.trans (by decide +kernel)
  upper_error := v1705_upper_checked
  lower_error := reuse_lower_error 19 53 Primitive.Addresses.material1705

def v1706_pa : Scalar.QComplex := ((999999739680370659329333003525 : Int)/10^30,(-721553318137358380153633268 : Int)/10^30)
theorem v1706_pa_checked : Scalar.distance (sourceCoefficient 19 54 1 0) v1706_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1706_pb : Scalar.QComplex := ((-311334023158670850412263 : Int)/10^30,(-431477389524035568649897020 : Int)/10^30)
theorem v1706_pb_checked : Scalar.distance (sourceCoefficient 19 54 1 1) v1706_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1706_pg : Scalar.QComplex := ((-93086403598561732007151 : Int)/10^30,(67166820874857469504 : Int)/10^30)
theorem v1706_pg_checked : Scalar.distance (sourceCoefficient 19 54 1 2) v1706_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1706_mb : Scalar.QComplex := ((-683679461373791514154373 : Int)/10^30,(-431476960198043935937948970 : Int)/10^30)
theorem v1706_mb_checked : Scalar.distance (sourceCoefficient 19 54 3 1) v1706_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1706_mg : Scalar.QComplex := ((-93086310976298079767425 : Int)/10^30,(147496169715152359680 : Int)/10^30)
theorem v1706_mg_checked : Scalar.distance (sourceCoefficient 19 54 3 2) v1706_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1706_upper : Scalar.QComplex := ((999997004962658327137294354386 : Int)/10^30,(-2447461074889046605456386866 : Int)/10^30)
theorem v1706_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 54 5) 1) 14) v1706_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1706 : Material (19 : Basis) (54 : Basis) where
  plus := ![v1706_pa,v1706_pb,v1706_pg]
  minus := ![(Primitive.Addresses.material1706 1).one,v1706_mb,v1706_mg]
  upper := v1706_upper
  lower := (Primitive.Addresses.material1706 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1706_pa_checked.trans (by decide +kernel)
    · exact v1706_pb_checked.trans (by decide +kernel)
    · exact v1706_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 54 Primitive.Addresses.material1706
    · exact v1706_mb_checked.trans (by decide +kernel)
    · exact v1706_mg_checked.trans (by decide +kernel)
  upper_error := v1706_upper_checked
  lower_error := reuse_lower_error 19 54 Primitive.Addresses.material1706

def v1707_pa : Scalar.QComplex := ((999999728491435093074093475651 : Int)/10^30,(-736896910087802576904951021 : Int)/10^30)
theorem v1707_pa_checked : Scalar.distance (sourceCoefficient 19 55 1 0) v1707_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1707_pb : Scalar.QComplex := ((-317954437031045424109641 : Int)/10^30,(-431477383540402814105850437 : Int)/10^30)
theorem v1707_pb_checked : Scalar.distance (sourceCoefficient 19 55 1 1) v1707_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1707_pg : Scalar.QComplex := ((-93086402432341912003773 : Int)/10^30,(68595100947739882994 : Int)/10^30)
theorem v1707_pg_checked : Scalar.distance (sourceCoefficient 19 55 1 2) v1707_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1707_mb : Scalar.QComplex := ((-690299867617477860949283 : Int)/10^30,(-431476948501294409886718340 : Int)/10^30)
theorem v1707_mb_checked : Scalar.distance (sourceCoefficient 19 55 3 1) v1707_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1707_mg : Scalar.QComplex := ((-93086308577537318450001 : Int)/10^30,(148924448249825646339 : Int)/10^30)
theorem v1707_mg_checked : Scalar.distance (sourceCoefficient 19 55 3 2) v1707_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1707_upper : Scalar.QComplex := ((999996967292091678808903616878 : Int)/10^30,(-2462804624675925241891081690 : Int)/10^30)
theorem v1707_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 55 5) 1) 14) v1707_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1707 : Material (19 : Basis) (55 : Basis) where
  plus := ![v1707_pa,v1707_pb,v1707_pg]
  minus := ![(Primitive.Addresses.material1707 1).one,v1707_mb,v1707_mg]
  upper := v1707_upper
  lower := (Primitive.Addresses.material1707 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1707_pa_checked.trans (by decide +kernel)
    · exact v1707_pb_checked.trans (by decide +kernel)
    · exact v1707_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 55 Primitive.Addresses.material1707
    · exact v1707_mb_checked.trans (by decide +kernel)
    · exact v1707_mg_checked.trans (by decide +kernel)
  upper_error := v1707_upper_checked
  lower_error := reuse_lower_error 19 55 Primitive.Addresses.material1707

def v1708_pa : Scalar.QComplex := ((999999725801421450900081011245 : Int)/10^30,(-740538373018805393242084969 : Int)/10^30)
theorem v1708_pa_checked : Scalar.distance (sourceCoefficient 19 56 1 0) v1708_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1708_pb : Scalar.QComplex := ((-319525646148546277958964 : Int)/10^30,(-431477382100433291387895413 : Int)/10^30)
theorem v1708_pb_checked : Scalar.distance (sourceCoefficient 19 56 1 1) v1708_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1708_pg : Scalar.QComplex := ((-93086402151811401612365 : Int)/10^30,(68934071701301114849 : Int)/10^30)
theorem v1708_pg_checked : Scalar.distance (sourceCoefficient 19 56 1 2) v1708_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1708_mb : Scalar.QComplex := ((-691871074907316908263212 : Int)/10^30,(-431476945705442719563735239 : Int)/10^30)
theorem v1708_mb_checked : Scalar.distance (sourceCoefficient 19 56 3 1) v1708_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1708_mg : Scalar.QComplex := ((-93086308004490418865595 : Int)/10^30,(149263418635087379072 : Int)/10^30)
theorem v1708_mg_checked : Scalar.distance (sourceCoefficient 19 56 3 2) v1708_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1708_upper : Scalar.QComplex := ((999996958317247375119899649408 : Int)/10^30,(-2466446077540677268522603248 : Int)/10^30)
theorem v1708_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 56 5) 1) 14) v1708_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1708 : Material (19 : Basis) (56 : Basis) where
  plus := ![v1708_pa,v1708_pb,v1708_pg]
  minus := ![(Primitive.Addresses.material1708 1).one,v1708_mb,v1708_mg]
  upper := v1708_upper
  lower := (Primitive.Addresses.material1708 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1708_pa_checked.trans (by decide +kernel)
    · exact v1708_pb_checked.trans (by decide +kernel)
    · exact v1708_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 56 Primitive.Addresses.material1708
    · exact v1708_mb_checked.trans (by decide +kernel)
    · exact v1708_mg_checked.trans (by decide +kernel)
  upper_error := v1708_upper_checked
  lower_error := reuse_lower_error 19 56 Primitive.Addresses.material1708

def v1709_pa : Scalar.QComplex := ((999999717010107937808916784145 : Int)/10^30,(-752316226091863020014611917 : Int)/10^30)
theorem v1709_pa_checked : Scalar.distance (sourceCoefficient 19 57 1 0) v1709_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1709_pb : Scalar.QComplex := ((-324607524063304777980182 : Int)/10^30,(-431477377390793862493888204 : Int)/10^30)
theorem v1709_pb_checked : Scalar.distance (sourceCoefficient 19 57 1 1) v1709_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1709_pg : Scalar.QComplex := ((-93086401234609497007087 : Int)/10^30,(70030429895198152423 : Int)/10^30)
theorem v1709_pg_checked : Scalar.distance (sourceCoefficient 19 57 1 2) v1709_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1709_mb : Scalar.QComplex := ((-696952946865653294475887 : Int)/10^30,(-431476936610373283132025335 : Int)/10^30)
theorem v1709_mb_checked : Scalar.distance (sourceCoefficient 19 57 3 1) v1709_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1709_mg : Scalar.QComplex := ((-93086306141181112583411 : Int)/10^30,(150359775629256220579 : Int)/10^30)
theorem v1709_mg_checked : Scalar.distance (sourceCoefficient 19 57 3 2) v1709_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1709_upper : Scalar.QComplex := ((999996929198441030044341044612 : Int)/10^30,(-2478223897898996684921507388 : Int)/10^30)
theorem v1709_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 57 5) 1) 14) v1709_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1709 : Material (19 : Basis) (57 : Basis) where
  plus := ![v1709_pa,v1709_pb,v1709_pg]
  minus := ![(Primitive.Addresses.material1709 1).one,v1709_mb,v1709_mg]
  upper := v1709_upper
  lower := (Primitive.Addresses.material1709 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1709_pa_checked.trans (by decide +kernel)
    · exact v1709_pb_checked.trans (by decide +kernel)
    · exact v1709_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 57 Primitive.Addresses.material1709
    · exact v1709_mb_checked.trans (by decide +kernel)
    · exact v1709_mg_checked.trans (by decide +kernel)
  upper_error := v1709_upper_checked
  lower_error := reuse_lower_error 19 57 Primitive.Addresses.material1709

def v1710_pa : Scalar.QComplex := ((999999712181973700160489702168 : Int)/10^30,(-758706774558170633355253117 : Int)/10^30)
theorem v1710_pa_checked : Scalar.distance (sourceCoefficient 19 58 1 0) v1710_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1710_pb : Scalar.QComplex := ((-327364901552365491067506 : Int)/10^30,(-431477374801991219407135016 : Int)/10^30)
theorem v1710_pb_checked : Scalar.distance (sourceCoefficient 19 58 1 1) v1710_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1710_pg : Scalar.QComplex := ((-93086400730640057644618 : Int)/10^30,(70625303180808624671 : Int)/10^30)
theorem v1710_pg_checked : Scalar.distance (sourceCoefficient 19 58 1 2) v1710_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1710_mb : Scalar.QComplex := ((-699710321093996264368178 : Int)/10^30,(-431476931642079018587459110 : Int)/10^30)
theorem v1710_mb_checked : Scalar.distance (sourceCoefficient 19 58 3 1) v1710_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1710_mg : Scalar.QComplex := ((-93086305123863007488174 : Int)/10^30,(150954648258465253314 : Int)/10^30)
theorem v1710_mg_checked : Scalar.distance (sourceCoefficient 19 58 3 2) v1710_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1710_upper : Scalar.QComplex := ((999996913340807076515903810337 : Int)/10^30,(-2484614428514411354988013100 : Int)/10^30)
theorem v1710_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 58 5) 1) 14) v1710_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1710 : Material (19 : Basis) (58 : Basis) where
  plus := ![v1710_pa,v1710_pb,v1710_pg]
  minus := ![(Primitive.Addresses.material1710 1).one,v1710_mb,v1710_mg]
  upper := v1710_upper
  lower := (Primitive.Addresses.material1710 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1710_pa_checked.trans (by decide +kernel)
    · exact v1710_pb_checked.trans (by decide +kernel)
    · exact v1710_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 58 Primitive.Addresses.material1710
    · exact v1710_mb_checked.trans (by decide +kernel)
    · exact v1710_mg_checked.trans (by decide +kernel)
  upper_error := v1710_upper_checked
  lower_error := reuse_lower_error 19 58 Primitive.Addresses.material1710

def v1711_pa : Scalar.QComplex := ((999999698700305015733484413042 : Int)/10^30,(-776272696407020896556314076 : Int)/10^30)
theorem v1711_pa_checked : Scalar.distance (sourceCoefficient 19 59 1 0) v1711_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1711_pb : Scalar.QComplex := ((-334944200476879657259248 : Int)/10^30,(-431477367565010829437086562 : Int)/10^30)
theorem v1711_pb_checked : Scalar.distance (sourceCoefficient 19 59 1 1) v1711_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1711_pg : Scalar.QComplex := ((-93086399322511228131100 : Int)/10^30,(72260451972958613139 : Int)/10^30)
theorem v1711_pg_checked : Scalar.distance (sourceCoefficient 19 59 1 2) v1711_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1711_mb : Scalar.QComplex := ((-707289610951202914843475 : Int)/10^30,(-431476917864507710371950947 : Int)/10^30)
theorem v1711_mb_checked : Scalar.distance (sourceCoefficient 19 59 3 1) v1711_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1711_mg : Scalar.QComplex := ((-93086302304674939027725 : Int)/10^30,(152589795226622856370 : Int)/10^30)
theorem v1711_mg_checked : Scalar.distance (sourceCoefficient 19 59 3 2) v1711_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1711_upper : Scalar.QComplex := ((999996869541970928317039402550 : Int)/10^30,(-2502180300932747360563713698 : Int)/10^30)
theorem v1711_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 59 5) 1) 14) v1711_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1711 : Material (19 : Basis) (59 : Basis) where
  plus := ![v1711_pa,v1711_pb,v1711_pg]
  minus := ![(Primitive.Addresses.material1711 1).one,v1711_mb,v1711_mg]
  upper := v1711_upper
  lower := (Primitive.Addresses.material1711 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1711_pa_checked.trans (by decide +kernel)
    · exact v1711_pb_checked.trans (by decide +kernel)
    · exact v1711_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 59 Primitive.Addresses.material1711
    · exact v1711_mb_checked.trans (by decide +kernel)
    · exact v1711_mg_checked.trans (by decide +kernel)
  upper_error := v1711_upper_checked
  lower_error := reuse_lower_error 19 59 Primitive.Addresses.material1711

def v1712_pa : Scalar.QComplex := ((999999682764655908893987212264 : Int)/10^30,(-796536620340802965754980083 : Int)/10^30)
theorem v1712_pa_checked : Scalar.distance (sourceCoefficient 19 60 1 0) v1712_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1712_pb : Scalar.QComplex := ((-343687626318089816129629 : Int)/10^30,(-431477358995972661813075536 : Int)/10^30)
theorem v1712_pb_checked : Scalar.distance (sourceCoefficient 19 60 1 1) v1712_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1712_pg : Scalar.QComplex := ((-93086397656478006549370 : Int)/10^30,(74146748110960183051 : Int)/10^30)
theorem v1712_pg_checked : Scalar.distance (sourceCoefficient 19 60 1 2) v1712_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1712_mb : Scalar.QComplex := ((-716033026142142035222973 : Int)/10^30,(-431476901750290021709849848 : Int)/10^30)
theorem v1712_mb_checked : Scalar.distance (sourceCoefficient 19 60 3 1) v1712_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1712_mg : Scalar.QComplex := ((-93086299010853726315305 : Int)/10^30,(154476089224558531238 : Int)/10^30)
theorem v1712_mg_checked : Scalar.distance (sourceCoefficient 19 60 3 2) v1712_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1712_upper : Scalar.QComplex := ((999996818632651174866138603800 : Int)/10^30,(-2522444167182310410500001625 : Int)/10^30)
theorem v1712_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 19 60 5) 1) 14) v1712_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1712 : Material (19 : Basis) (60 : Basis) where
  plus := ![v1712_pa,v1712_pb,v1712_pg]
  minus := ![(Primitive.Addresses.material1712 1).one,v1712_mb,v1712_mg]
  upper := v1712_upper
  lower := (Primitive.Addresses.material1712 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1712_pa_checked.trans (by decide +kernel)
    · exact v1712_pb_checked.trans (by decide +kernel)
    · exact v1712_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 19 60 Primitive.Addresses.material1712
    · exact v1712_mb_checked.trans (by decide +kernel)
    · exact v1712_mg_checked.trans (by decide +kernel)
  upper_error := v1712_upper_checked
  lower_error := reuse_lower_error 19 60 Primitive.Addresses.material1712

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
