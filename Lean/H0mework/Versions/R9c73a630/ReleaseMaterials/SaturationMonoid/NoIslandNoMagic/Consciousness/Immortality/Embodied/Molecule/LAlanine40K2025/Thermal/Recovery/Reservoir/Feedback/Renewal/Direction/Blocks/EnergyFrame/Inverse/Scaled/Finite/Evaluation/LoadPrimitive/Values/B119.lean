import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B079
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B080

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1905_pa : Scalar.QComplex := ((999999918347273038854869643699 : Int)/10^30,(-404110686885564114650833443 : Int)/10^30)
theorem v1905_pa_checked : Scalar.distance (sourceCoefficient 22 25 1 0) v1905_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1905_pb : Scalar.QComplex := ((-174364677181032490658353 : Int)/10^30,(-431477485259026621983750770 : Int)/10^30)
theorem v1905_pb_checked : Scalar.distance (sourceCoefficient 22 25 1 1) v1905_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1905_pg : Scalar.QComplex := ((-93086422241168397906821 : Int)/10^30,(37617221103146897590 : Int)/10^30)
theorem v1905_pg_checked : Scalar.distance (sourceCoefficient 22 25 1 2) v1905_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1905_mb : Scalar.QComplex := ((-546710249011086005316741 : Int)/10^30,(-431477174131376051117631322 : Int)/10^30)
theorem v1905_mb_checked : Scalar.distance (sourceCoefficient 22 25 3 1) v1905_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1905_mg : Scalar.QComplex := ((-93086355118871542589145 : Int)/10^30,(117946597033838187034 : Int)/10^30)
theorem v1905_mg_checked : Scalar.distance (sourceCoefficient 22 25 3 2) v1905_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1905_upper : Scalar.QComplex := ((999997731506477973348127768119 : Int)/10^30,(-2130019224793627130885987627 : Int)/10^30)
theorem v1905_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 25 5) 1) 14) v1905_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1905 : Material (22 : Basis) (25 : Basis) where
  plus := ![v1905_pa,v1905_pb,v1905_pg]
  minus := ![(Primitive.Addresses.material1905 1).one,v1905_mb,v1905_mg]
  upper := v1905_upper
  lower := (Primitive.Addresses.material1905 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1905_pa_checked.trans (by decide +kernel)
    · exact v1905_pb_checked.trans (by decide +kernel)
    · exact v1905_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 25 Primitive.Addresses.material1905
    · exact v1905_mb_checked.trans (by decide +kernel)
    · exact v1905_mg_checked.trans (by decide +kernel)
  upper_error := v1905_upper_checked
  lower_error := reuse_lower_error 22 25 Primitive.Addresses.material1905

def v1906_pa : Scalar.QComplex := ((999999915352545432461603785873 : Int)/10^30,(-411454617144935229446909795 : Int)/10^30)
theorem v1906_pa_checked : Scalar.distance (sourceCoefficient 22 26 1 0) v1906_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1906_pb : Scalar.QComplex := ((-177533417961794006882694 : Int)/10^30,(-431477483874013224684449125 : Int)/10^30)
theorem v1906_pb_checked : Scalar.distance (sourceCoefficient 22 26 1 1) v1906_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1906_pg : Scalar.QComplex := ((-93086421952383603542511 : Int)/10^30,(38300841347878617650 : Int)/10^30)
theorem v1906_pg_checked : Scalar.distance (sourceCoefficient 22 26 1 2) v1906_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1906_mb : Scalar.QComplex := ((-549878987416776327074216 : Int)/10^30,(-431477170011882590511870811 : Int)/10^30)
theorem v1906_mb_checked : Scalar.distance (sourceCoefficient 22 26 3 1) v1906_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1906_mg : Scalar.QComplex := ((-93086354240153373662015 : Int)/10^30,(118630216774818575839 : Int)/10^30)
theorem v1906_mg_checked : Scalar.distance (sourceCoefficient 22 26 3 2) v1906_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1906_upper : Scalar.QComplex := ((999997715836797435724081038504 : Int)/10^30,(-2137363138946448633928354867 : Int)/10^30)
theorem v1906_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 26 5) 1) 14) v1906_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1906 : Material (22 : Basis) (26 : Basis) where
  plus := ![v1906_pa,v1906_pb,v1906_pg]
  minus := ![(Primitive.Addresses.material1906 1).one,v1906_mb,v1906_mg]
  upper := v1906_upper
  lower := (Primitive.Addresses.material1906 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1906_pa_checked.trans (by decide +kernel)
    · exact v1906_pb_checked.trans (by decide +kernel)
    · exact v1906_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 26 Primitive.Addresses.material1906
    · exact v1906_mb_checked.trans (by decide +kernel)
    · exact v1906_mg_checked.trans (by decide +kernel)
  upper_error := v1906_upper_checked
  lower_error := reuse_lower_error 22 26 Primitive.Addresses.material1906

def v1907_pa : Scalar.QComplex := ((999999913263933633037599452878 : Int)/10^30,(-416499850192985774476142990 : Int)/10^30)
theorem v1907_pa_checked : Scalar.distance (sourceCoefficient 22 27 1 0) v1907_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1907_pb : Scalar.QComplex := ((-179710322578753069566720 : Int)/10^30,(-431477482904537870398809677 : Int)/10^30)
theorem v1907_pb_checked : Scalar.distance (sourceCoefficient 22 27 1 1) v1907_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1907_pg : Scalar.QComplex := ((-93086421750596185182427 : Int)/10^30,(38770484076923683709 : Int)/10^30)
theorem v1907_pg_checked : Scalar.distance (sourceCoefficient 22 27 1 2) v1907_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1907_mb : Scalar.QComplex := ((-552055890386560744209093 : Int)/10^30,(-431477167163836956914919997 : Int)/10^30)
theorem v1907_mb_checked : Scalar.distance (sourceCoefficient 22 27 3 1) v1907_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1907_mg : Scalar.QComplex := ((-93086353633085507194037 : Int)/10^30,(119099859154860736265 : Int)/10^30)
theorem v1907_mg_checked : Scalar.distance (sourceCoefficient 22 27 3 2) v1907_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1907_upper : Scalar.QComplex := ((999997705040574206073528865432 : Int)/10^30,(-2142408360875462720168343850 : Int)/10^30)
theorem v1907_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 27 5) 1) 14) v1907_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1907 : Material (22 : Basis) (27 : Basis) where
  plus := ![v1907_pa,v1907_pb,v1907_pg]
  minus := ![(Primitive.Addresses.material1907 1).one,v1907_mb,v1907_mg]
  upper := v1907_upper
  lower := (Primitive.Addresses.material1907 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1907_pa_checked.trans (by decide +kernel)
    · exact v1907_pb_checked.trans (by decide +kernel)
    · exact v1907_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 27 Primitive.Addresses.material1907
    · exact v1907_mb_checked.trans (by decide +kernel)
    · exact v1907_mg_checked.trans (by decide +kernel)
  upper_error := v1907_upper_checked
  lower_error := reuse_lower_error 22 27 Primitive.Addresses.material1907

def v1908_pa : Scalar.QComplex := ((999999910410060406321601027954 : Int)/10^30,(-423296434146331454240096872 : Int)/10^30)
theorem v1908_pa_checked : Scalar.distance (sourceCoefficient 22 28 1 0) v1908_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1908_pb : Scalar.QComplex := ((-182642895728262662989871 : Int)/10^30,(-431477481575377363395263752 : Int)/10^30)
theorem v1908_pb_checked : Scalar.distance (sourceCoefficient 22 28 1 1) v1908_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1908_pg : Scalar.QComplex := ((-93086421474392023433676 : Int)/10^30,(39403153807678806692 : Int)/10^30)
theorem v1908_pg_checked : Scalar.distance (sourceCoefficient 22 28 1 2) v1908_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1908_mb : Scalar.QComplex := ((-554988461297133674478860 : Int)/10^30,(-431477163303998394983478311 : Int)/10^30)
theorem v1908_mb_checked : Scalar.distance (sourceCoefficient 22 28 3 1) v1908_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1908_mg : Scalar.QComplex := ((-93086352810915965033959 : Int)/10^30,(119732528411692252238 : Int)/10^30)
theorem v1908_mg_checked : Scalar.distance (sourceCoefficient 22 28 3 2) v1908_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1908_upper : Scalar.QComplex := ((999997690456417907671597745388 : Int)/10^30,(-2149204929780568696303290945 : Int)/10^30)
theorem v1908_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 28 5) 1) 14) v1908_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1908 : Material (22 : Basis) (28 : Basis) where
  plus := ![v1908_pa,v1908_pb,v1908_pg]
  minus := ![(Primitive.Addresses.material1908 1).one,v1908_mb,v1908_mg]
  upper := v1908_upper
  lower := (Primitive.Addresses.material1908 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1908_pa_checked.trans (by decide +kernel)
    · exact v1908_pb_checked.trans (by decide +kernel)
    · exact v1908_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 28 Primitive.Addresses.material1908
    · exact v1908_mb_checked.trans (by decide +kernel)
    · exact v1908_mg_checked.trans (by decide +kernel)
  upper_error := v1908_upper_checked
  lower_error := reuse_lower_error 22 28 Primitive.Addresses.material1908

def v1909_pa : Scalar.QComplex := ((999999904488491286389371762957 : Int)/10^30,(-437061790030623655894317484 : Int)/10^30)
theorem v1909_pa_checked : Scalar.distance (sourceCoefficient 22 29 1 0) v1909_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1909_pb : Scalar.QComplex := ((-188582337254870889055685 : Int)/10^30,(-431477478801965102616376203 : Int)/10^30)
theorem v1909_pb_checked : Scalar.distance (sourceCoefficient 22 29 1 1) v1909_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1909_pg : Scalar.QComplex := ((-93086420899616883589454 : Int)/10^30,(40684521631770654320 : Int)/10^30)
theorem v1909_pg_checked : Scalar.distance (sourceCoefficient 22 29 1 2) v1909_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1909_mb : Scalar.QComplex := ((-560927898218886503100140 : Int)/10^30,(-431477155405116631926025819 : Int)/10^30)
theorem v1909_mb_checked : Scalar.distance (sourceCoefficient 22 29 3 1) v1909_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1909_mg : Scalar.QComplex := ((-93086351130378317678002 : Int)/10^30,(121013895262667238779 : Int)/10^30)
theorem v1909_mg_checked : Scalar.distance (sourceCoefficient 22 29 3 2) v1909_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1909_upper : Scalar.QComplex := ((999997660777102134263499136801 : Int)/10^30,(-2162970254942889200145111375 : Int)/10^30)
theorem v1909_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 29 5) 1) 14) v1909_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1909 : Material (22 : Basis) (29 : Basis) where
  plus := ![v1909_pa,v1909_pb,v1909_pg]
  minus := ![(Primitive.Addresses.material1909 1).one,v1909_mb,v1909_mg]
  upper := v1909_upper
  lower := (Primitive.Addresses.material1909 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1909_pa_checked.trans (by decide +kernel)
    · exact v1909_pb_checked.trans (by decide +kernel)
    · exact v1909_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 29 Primitive.Addresses.material1909
    · exact v1909_mb_checked.trans (by decide +kernel)
    · exact v1909_mg_checked.trans (by decide +kernel)
  upper_error := v1909_upper_checked
  lower_error := reuse_lower_error 22 29 Primitive.Addresses.material1909

def v1910_pa : Scalar.QComplex := ((999999902195042035395212411468 : Int)/10^30,(-442278087139075626077324960 : Int)/10^30)
theorem v1910_pa_checked : Scalar.distance (sourceCoefficient 22 30 1 0) v1910_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1910_pb : Scalar.QComplex := ((-190833052155126146332729 : Int)/10^30,(-431477477722516018956326303 : Int)/10^30)
theorem v1910_pb_checked : Scalar.distance (sourceCoefficient 22 30 1 1) v1910_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1910_pg : Scalar.QComplex := ((-93086420676432873127106 : Int)/10^30,(41170088102034765564 : Int)/10^30)
theorem v1910_pg_checked : Scalar.distance (sourceCoefficient 22 30 1 2) v1910_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1910_mb : Scalar.QComplex := ((-563178611349581797643060 : Int)/10^30,(-431477152383402359710050264 : Int)/10^30)
theorem v1910_mb_checked : Scalar.distance (sourceCoefficient 22 30 3 1) v1910_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1910_mg : Scalar.QComplex := ((-93086350488172395581335 : Int)/10^30,(121499461359535012466 : Int)/10^30)
theorem v1910_mg_checked : Scalar.distance (sourceCoefficient 22 30 3 2) v1910_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1910_upper : Scalar.QComplex := ((999997649480800708681587669919 : Int)/10^30,(-2168186540323994029465413741 : Int)/10^30)
theorem v1910_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 30 5) 1) 14) v1910_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1910 : Material (22 : Basis) (30 : Basis) where
  plus := ![v1910_pa,v1910_pb,v1910_pg]
  minus := ![(Primitive.Addresses.material1910 1).one,v1910_mb,v1910_mg]
  upper := v1910_upper
  lower := (Primitive.Addresses.material1910 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1910_pa_checked.trans (by decide +kernel)
    · exact v1910_pb_checked.trans (by decide +kernel)
    · exact v1910_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 30 Primitive.Addresses.material1910
    · exact v1910_mb_checked.trans (by decide +kernel)
    · exact v1910_mg_checked.trans (by decide +kernel)
  upper_error := v1910_upper_checked
  lower_error := reuse_lower_error 22 30 Primitive.Addresses.material1910

def v1911_pa : Scalar.QComplex := ((999999897226385648001154116242 : Int)/10^30,(-453373155514948728634980638 : Int)/10^30)
theorem v1911_pa_checked : Scalar.distance (sourceCoefficient 22 31 1 0) v1911_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1911_pb : Scalar.QComplex := ((-195620324648754363523375 : Int)/10^30,(-431477475374468921259279530 : Int)/10^30)
theorem v1911_pb_checked : Scalar.distance (sourceCoefficient 22 31 1 1) v1911_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1911_pg : Scalar.QComplex := ((-93086420191893234061077 : Int)/10^30,(42202888395332451163 : Int)/10^30)
theorem v1911_pg_checked : Scalar.distance (sourceCoefficient 22 31 1 2) v1911_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1911_mb : Scalar.QComplex := ((-567965880034430783097583 : Int)/10^30,(-431477145904155585046363360 : Int)/10^30)
theorem v1911_mb_checked : Scalar.distance (sourceCoefficient 22 31 3 1) v1911_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1911_mg : Scalar.QComplex := ((-93086349112372799414125 : Int)/10^30,(122532260850138061906 : Int)/10^30)
theorem v1911_mg_checked : Scalar.distance (sourceCoefficient 22 31 3 2) v1911_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1911_upper : Scalar.QComplex := ((999997625363070241501009684868 : Int)/10^30,(-2179281583599615932788859933 : Int)/10^30)
theorem v1911_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 31 5) 1) 14) v1911_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1911 : Material (22 : Basis) (31 : Basis) where
  plus := ![v1911_pa,v1911_pb,v1911_pg]
  minus := ![(Primitive.Addresses.material1911 1).one,v1911_mb,v1911_mg]
  upper := v1911_upper
  lower := (Primitive.Addresses.material1911 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1911_pa_checked.trans (by decide +kernel)
    · exact v1911_pb_checked.trans (by decide +kernel)
    · exact v1911_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 31 Primitive.Addresses.material1911
    · exact v1911_mb_checked.trans (by decide +kernel)
    · exact v1911_mg_checked.trans (by decide +kernel)
  upper_error := v1911_upper_checked
  lower_error := reuse_lower_error 22 31 Primitive.Addresses.material1911

def v1912_pa : Scalar.QComplex := ((999999895049629106359374449940 : Int)/10^30,(-458149245085813603578051583 : Int)/10^30)
theorem v1912_pa_checked : Scalar.distance (sourceCoefficient 22 32 1 0) v1912_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1912_pb : Scalar.QComplex := ((-197681099887980407075576 : Int)/10^30,(-431477474341901443563827318 : Int)/10^30)
theorem v1912_pb_checked : Scalar.distance (sourceCoefficient 22 32 1 1) v1912_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1912_pg : Scalar.QComplex := ((-93086419979197567470868 : Int)/10^30,(42647477517078945481 : Int)/10^30)
theorem v1912_pg_checked : Scalar.distance (sourceCoefficient 22 32 1 2) v1912_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1912_mb : Scalar.QComplex := ((-570026653615276794866476 : Int)/10^30,(-431477143093232274242260056 : Int)/10^30)
theorem v1912_mb_checked : Scalar.distance (sourceCoefficient 22 32 3 1) v1912_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1912_mg : Scalar.QComplex := ((-93086348516016823503743 : Int)/10^30,(122976849622796926661 : Int)/10^30)
theorem v1912_mg_checked : Scalar.distance (sourceCoefficient 22 32 3 2) v1912_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1912_upper : Scalar.QComplex := ((999997614943219626030869061916 : Int)/10^30,(-2184057662300172113757691346 : Int)/10^30)
theorem v1912_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 32 5) 1) 14) v1912_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1912 : Material (22 : Basis) (32 : Basis) where
  plus := ![v1912_pa,v1912_pb,v1912_pg]
  minus := ![(Primitive.Addresses.material1912 1).one,v1912_mb,v1912_mg]
  upper := v1912_upper
  lower := (Primitive.Addresses.material1912 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1912_pa_checked.trans (by decide +kernel)
    · exact v1912_pb_checked.trans (by decide +kernel)
    · exact v1912_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 32 Primitive.Addresses.material1912
    · exact v1912_mb_checked.trans (by decide +kernel)
    · exact v1912_mg_checked.trans (by decide +kernel)
  upper_error := v1912_upper_checked
  lower_error := reuse_lower_error 22 32 Primitive.Addresses.material1912

def v1913_pa : Scalar.QComplex := ((999999891977981909226209310507 : Int)/10^30,(-464805361966480749176902663 : Int)/10^30)
theorem v1913_pa_checked : Scalar.distance (sourceCoefficient 22 33 1 0) v1913_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1913_pb : Scalar.QComplex := ((-200553064626978897702754 : Int)/10^30,(-431477472880992547683062965 : Int)/10^30)
theorem v1913_pb_checked : Scalar.distance (sourceCoefficient 22 33 1 1) v1913_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1913_pg : Scalar.QComplex := ((-93086419678645887319889 : Int)/10^30,(43267071666693136590 : Int)/10^30)
theorem v1913_pg_checked : Scalar.distance (sourceCoefficient 22 33 1 2) v1913_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1913_mb : Scalar.QComplex := ((-572898616024212977640876 : Int)/10^30,(-431477139153947701059149895 : Int)/10^30)
theorem v1913_mb_checked : Scalar.distance (sourceCoefficient 22 33 3 1) v1913_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1913_mg : Scalar.QComplex := ((-93086347680783409629442 : Int)/10^30,(123596443282345335392 : Int)/10^30)
theorem v1913_mg_checked : Scalar.distance (sourceCoefficient 22 33 3 2) v1913_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1913_upper : Scalar.QComplex := ((999997600383723105930378634270 : Int)/10^30,(-2190713763965950643421002817 : Int)/10^30)
theorem v1913_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 33 5) 1) 14) v1913_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1913 : Material (22 : Basis) (33 : Basis) where
  plus := ![v1913_pa,v1913_pb,v1913_pg]
  minus := ![(Primitive.Addresses.material1913 1).one,v1913_mb,v1913_mg]
  upper := v1913_upper
  lower := (Primitive.Addresses.material1913 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1913_pa_checked.trans (by decide +kernel)
    · exact v1913_pb_checked.trans (by decide +kernel)
    · exact v1913_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 33 Primitive.Addresses.material1913
    · exact v1913_mb_checked.trans (by decide +kernel)
    · exact v1913_mg_checked.trans (by decide +kernel)
  upper_error := v1913_upper_checked
  lower_error := reuse_lower_error 22 33 Primitive.Addresses.material1913

def v1914_pa : Scalar.QComplex := ((999999884332804419107310088771 : Int)/10^30,(-480972325381497647633298827 : Int)/10^30)
theorem v1914_pa_checked : Scalar.distance (sourceCoefficient 22 34 1 0) v1914_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1914_pb : Scalar.QComplex := ((-207528745727847140673387 : Int)/10^30,(-431477469226470525921581332 : Int)/10^30)
theorem v1914_pb_checked : Scalar.distance (sourceCoefficient 22 34 1 1) v1914_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1914_pg : Scalar.QComplex := ((-93086418928603704459336 : Int)/10^30,(44771996552178064333 : Int)/10^30)
theorem v1914_pg_checked : Scalar.distance (sourceCoefficient 22 34 1 2) v1914_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1914_mb : Scalar.QComplex := ((-579874291374028431164398 : Int)/10^30,(-431477129479728423008075802 : Int)/10^30)
theorem v1914_mb_checked : Scalar.distance (sourceCoefficient 22 34 3 1) v1914_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1914_mg : Scalar.QComplex := ((-93086345632059109171136 : Int)/10^30,(125101366960225326641 : Int)/10^30)
theorem v1914_mg_checked : Scalar.distance (sourceCoefficient 22 34 3 2) v1914_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1914_upper : Scalar.QComplex := ((999997564835844803550245157854 : Int)/10^30,(-2206880690107291857276152093 : Int)/10^30)
theorem v1914_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 34 5) 1) 14) v1914_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1914 : Material (22 : Basis) (34 : Basis) where
  plus := ![v1914_pa,v1914_pb,v1914_pg]
  minus := ![(Primitive.Addresses.material1914 1).one,v1914_mb,v1914_mg]
  upper := v1914_upper
  lower := (Primitive.Addresses.material1914 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1914_pa_checked.trans (by decide +kernel)
    · exact v1914_pb_checked.trans (by decide +kernel)
    · exact v1914_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 34 Primitive.Addresses.material1914
    · exact v1914_mb_checked.trans (by decide +kernel)
    · exact v1914_mg_checked.trans (by decide +kernel)
  upper_error := v1914_upper_checked
  lower_error := reuse_lower_error 22 34 Primitive.Addresses.material1914

def v1915_pa : Scalar.QComplex := ((999999858310021070755997724833 : Int)/10^30,(-532334422879488299187259175 : Int)/10^30)
theorem v1915_pa_checked : Scalar.distance (sourceCoefficient 22 35 1 0) v1915_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1915_pb : Scalar.QComplex := ((-229690335399300646318428 : Int)/10^30,(-431477456618430902222482091 : Int)/10^30)
theorem v1915_pb_checked : Scalar.distance (sourceCoefficient 22 35 1 1) v1915_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1915_pg : Scalar.QComplex := ((-93086416357398223050509 : Int)/10^30,(49553110750714560638 : Int)/10^30)
theorem v1915_pg_checked : Scalar.distance (sourceCoefficient 22 35 1 2) v1915_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1915_mb : Scalar.QComplex := ((-602035861913538917217196 : Int)/10^30,(-431477097747239728340780045 : Int)/10^30)
theorem v1915_mb_checked : Scalar.distance (sourceCoefficient 22 35 3 1) v1915_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1915_mg : Scalar.QComplex := ((-93086338934968365192574 : Int)/10^30,(129882477159699971458 : Int)/10^30)
theorem v1915_mg_checked : Scalar.distance (sourceCoefficient 22 35 3 2) v1915_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1915_upper : Scalar.QComplex := ((999997450166779464632757433951 : Int)/10^30,(-2258242666194508410579180705 : Int)/10^30)
theorem v1915_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 35 5) 1) 14) v1915_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1915 : Material (22 : Basis) (35 : Basis) where
  plus := ![v1915_pa,v1915_pb,v1915_pg]
  minus := ![(Primitive.Addresses.material1915 1).one,v1915_mb,v1915_mg]
  upper := v1915_upper
  lower := (Primitive.Addresses.material1915 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1915_pa_checked.trans (by decide +kernel)
    · exact v1915_pb_checked.trans (by decide +kernel)
    · exact v1915_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 35 Primitive.Addresses.material1915
    · exact v1915_mb_checked.trans (by decide +kernel)
    · exact v1915_mg_checked.trans (by decide +kernel)
  upper_error := v1915_upper_checked
  lower_error := reuse_lower_error 22 35 Primitive.Addresses.material1915

def v1916_pa : Scalar.QComplex := ((999999849585192823896135411738 : Int)/10^30,(-548479344850463362781379496 : Int)/10^30)
theorem v1916_pa_checked : Scalar.distance (sourceCoefficient 22 36 1 0) v1916_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1916_pb : Scalar.QComplex := ((-236656505974802761201160 : Int)/10^30,(-431477452341768194187104913 : Int)/10^30)
theorem v1916_pb_checked : Scalar.distance (sourceCoefficient 22 36 1 1) v1916_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1916_pg : Scalar.QComplex := ((-93086415489995689666679 : Int)/10^30,(51055983862006828168 : Int)/10^30)
theorem v1916_pg_checked : Scalar.distance (sourceCoefficient 22 36 1 2) v1916_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1916_mb : Scalar.QComplex := ((-609002026204650053821088 : Int)/10^30,(-431477087459087150720027849 : Int)/10^30)
theorem v1916_mb_checked : Scalar.distance (sourceCoefficient 22 36 3 1) v1916_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1916_mg : Scalar.QComplex := ((-93086336770654346629400 : Int)/10^30,(131385348962874575009 : Int)/10^30)
theorem v1916_mg_checked : Scalar.distance (sourceCoefficient 22 36 3 2) v1916_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1916_upper : Scalar.QComplex := ((999997413577293546356661736483 : Int)/10^30,(-2274387549061256670319114455 : Int)/10^30)
theorem v1916_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 36 5) 1) 14) v1916_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1916 : Material (22 : Basis) (36 : Basis) where
  plus := ![v1916_pa,v1916_pb,v1916_pg]
  minus := ![(Primitive.Addresses.material1916 1).one,v1916_mb,v1916_mg]
  upper := v1916_upper
  lower := (Primitive.Addresses.material1916 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1916_pa_checked.trans (by decide +kernel)
    · exact v1916_pb_checked.trans (by decide +kernel)
    · exact v1916_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 36 Primitive.Addresses.material1916
    · exact v1916_mb_checked.trans (by decide +kernel)
    · exact v1916_mg_checked.trans (by decide +kernel)
  upper_error := v1916_upper_checked
  lower_error := reuse_lower_error 22 36 Primitive.Addresses.material1916

def v1917_pa : Scalar.QComplex := ((999999845780181044873224394192 : Int)/10^30,(-555373400629253212580559203 : Int)/10^30)
theorem v1917_pa_checked : Scalar.distance (sourceCoefficient 22 37 1 0) v1917_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1917_pb : Scalar.QComplex := ((-239631135918178260357738 : Int)/10^30,(-431477450469898794541936993 : Int)/10^30)
theorem v1917_pb_checked : Scalar.distance (sourceCoefficient 22 37 1 1) v1917_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1917_pg : Scalar.QComplex := ((-93086415110980807293711 : Int)/10^30,(51697726885385794693 : Int)/10^30)
theorem v1917_pg_checked : Scalar.distance (sourceCoefficient 22 37 1 2) v1917_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1917_mb : Scalar.QComplex := ((-611976653425095891729022 : Int)/10^30,(-431477083020246779283692184 : Int)/10^30)
theorem v1917_mb_checked : Scalar.distance (sourceCoefficient 22 37 3 1) v1917_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1917_mg : Scalar.QComplex := ((-93086335837844279237788 : Int)/10^30,(132027091420230511534 : Int)/10^30)
theorem v1917_mg_checked : Scalar.distance (sourceCoefficient 22 37 3 2) v1917_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1917_upper : Scalar.QComplex := ((999997397873772584115255511752 : Int)/10^30,(-2281281588005055127668820616 : Int)/10^30)
theorem v1917_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 37 5) 1) 14) v1917_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1917 : Material (22 : Basis) (37 : Basis) where
  plus := ![v1917_pa,v1917_pb,v1917_pg]
  minus := ![(Primitive.Addresses.material1917 1).one,v1917_mb,v1917_mg]
  upper := v1917_upper
  lower := (Primitive.Addresses.material1917 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1917_pa_checked.trans (by decide +kernel)
    · exact v1917_pb_checked.trans (by decide +kernel)
    · exact v1917_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 37 Primitive.Addresses.material1917
    · exact v1917_mb_checked.trans (by decide +kernel)
    · exact v1917_mg_checked.trans (by decide +kernel)
  upper_error := v1917_upper_checked
  lower_error := reuse_lower_error 22 37 Primitive.Addresses.material1917

def v1918_pa : Scalar.QComplex := ((999999832567947914705960431675 : Int)/10^30,(-578674412893032634080359965 : Int)/10^30)
theorem v1918_pa_checked : Scalar.distance (sourceCoefficient 22 38 1 0) v1918_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1918_pb : Scalar.QComplex := ((-249684998354322936426827 : Int)/10^30,(-431477443940838788531959733 : Int)/10^30)
theorem v1918_pb_checked : Scalar.distance (sourceCoefficient 22 38 1 1) v1918_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1918_pg : Scalar.QComplex := ((-93086413791755312172022 : Int)/10^30,(53866734868279859155 : Int)/10^30)
theorem v1918_pg_checked : Scalar.distance (sourceCoefficient 22 38 1 2) v1918_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1918_mb : Scalar.QComplex := ((-622030506483443371369251 : Int)/10^30,(-431477067815158731103350500 : Int)/10^30)
theorem v1918_mb_checked : Scalar.distance (sourceCoefficient 22 38 3 1) v1918_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1918_mg : Scalar.QComplex := ((-93086332646863074579647 : Int)/10^30,(134196097457071588823 : Int)/10^30)
theorem v1918_mg_checked : Scalar.distance (sourceCoefficient 22 38 3 2) v1918_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1918_upper : Scalar.QComplex := ((999997344446125816054009234122 : Int)/10^30,(-2304582542761598133200401386 : Int)/10^30)
theorem v1918_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 38 5) 1) 14) v1918_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1918 : Material (22 : Basis) (38 : Basis) where
  plus := ![v1918_pa,v1918_pb,v1918_pg]
  minus := ![(Primitive.Addresses.material1918 1).one,v1918_mb,v1918_mg]
  upper := v1918_upper
  lower := (Primitive.Addresses.material1918 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1918_pa_checked.trans (by decide +kernel)
    · exact v1918_pb_checked.trans (by decide +kernel)
    · exact v1918_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 38 Primitive.Addresses.material1918
    · exact v1918_mb_checked.trans (by decide +kernel)
    · exact v1918_mg_checked.trans (by decide +kernel)
  upper_error := v1918_upper_checked
  lower_error := reuse_lower_error 22 38 Primitive.Addresses.material1918

def v1919_pa : Scalar.QComplex := ((999999824654418105352698537701 : Int)/10^30,(-592191804268871584112503935 : Int)/10^30)
theorem v1919_pa_checked : Scalar.distance (sourceCoefficient 22 39 1 0) v1919_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1919_pb : Scalar.QComplex := ((-255517448504713394459592 : Int)/10^30,(-431477440010037152356025832 : Int)/10^30)
theorem v1919_pb_checked : Scalar.distance (sourceCoefficient 22 39 1 1) v1919_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1919_pg : Scalar.QComplex := ((-93086412999421037525879 : Int)/10^30,(55125020532973288799 : Int)/10^30)
theorem v1919_pg_checked : Scalar.distance (sourceCoefficient 22 39 1 2) v1919_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1919_mb : Scalar.QComplex := ((-627862951070041306985585 : Int)/10^30,(-431477058851216762561039413 : Int)/10^30)
theorem v1919_mb_checked : Scalar.distance (sourceCoefficient 22 39 3 1) v1919_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1919_mg : Scalar.QComplex := ((-93086330768685237407944 : Int)/10^30,(135454381969498965398 : Int)/10^30)
theorem v1919_mg_checked : Scalar.distance (sourceCoefficient 22 39 3 2) v1919_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1919_upper : Scalar.QComplex := ((999997313202816566442160751851 : Int)/10^30,(-2318099900346835952125391816 : Int)/10^30)
theorem v1919_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 39 5) 1) 14) v1919_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1919 : Material (22 : Basis) (39 : Basis) where
  plus := ![v1919_pa,v1919_pb,v1919_pg]
  minus := ![(Primitive.Addresses.material1919 1).one,v1919_mb,v1919_mg]
  upper := v1919_upper
  lower := (Primitive.Addresses.material1919 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1919_pa_checked.trans (by decide +kernel)
    · exact v1919_pb_checked.trans (by decide +kernel)
    · exact v1919_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 39 Primitive.Addresses.material1919
    · exact v1919_mb_checked.trans (by decide +kernel)
    · exact v1919_mg_checked.trans (by decide +kernel)
  upper_error := v1919_upper_checked
  lower_error := reuse_lower_error 22 39 Primitive.Addresses.material1919

def v1920_pa : Scalar.QComplex := ((999999810932190736995180987074 : Int)/10^30,(-614927298775532601182742446 : Int)/10^30)
theorem v1920_pa_checked : Scalar.distance (sourceCoefficient 22 40 1 0) v1920_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1920_pb : Scalar.QComplex := ((-265327302621489552174832 : Int)/10^30,(-431477433161558704743093808 : Int)/10^30)
theorem v1920_pb_checked : Scalar.distance (sourceCoefficient 22 40 1 1) v1920_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1920_pg : Scalar.QComplex := ((-93086411622003300026993 : Int)/10^30,(57241386473929373375 : Int)/10^30)
theorem v1920_pg_checked : Scalar.distance (sourceCoefficient 22 40 1 2) v1920_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1920_mb : Scalar.QComplex := ((-637672795624231988273192 : Int)/10^30,(-431477043537278581600111732 : Int)/10^30)
theorem v1920_mb_checked : Scalar.distance (sourceCoefficient 22 40 3 1) v1920_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1920_mg : Scalar.QComplex := ((-93086327564939523323158 : Int)/10^30,(137570745933785816585 : Int)/10^30)
theorem v1920_mg_checked : Scalar.distance (sourceCoefficient 22 40 3 2) v1920_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1920_upper : Scalar.QComplex := ((999997260241208665183370737410 : Int)/10^30,(-2340835337308329033272541071 : Int)/10^30)
theorem v1920_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 40 5) 1) 14) v1920_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1920 : Material (22 : Basis) (40 : Basis) where
  plus := ![v1920_pa,v1920_pb,v1920_pg]
  minus := ![(Primitive.Addresses.material1920 1).one,v1920_mb,v1920_mg]
  upper := v1920_upper
  lower := (Primitive.Addresses.material1920 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1920_pa_checked.trans (by decide +kernel)
    · exact v1920_pb_checked.trans (by decide +kernel)
    · exact v1920_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 40 Primitive.Addresses.material1920
    · exact v1920_mb_checked.trans (by decide +kernel)
    · exact v1920_mg_checked.trans (by decide +kernel)
  upper_error := v1920_upper_checked
  lower_error := reuse_lower_error 22 40 Primitive.Addresses.material1920

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
