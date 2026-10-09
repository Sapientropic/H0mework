import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B114

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2737_pa : Scalar.QComplex := ((999999759573851534547935190903 : Int)/10^30,(-693435100875468564340159415 : Int)/10^30)
theorem v2737_pa_checked : Scalar.distance (sourceCoefficient 34 35 1 0) v2737_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2737_pb : Scalar.QComplex := ((-299201658169032417744459 : Int)/10^30,(-431477417072463183386019195 : Int)/10^30)
theorem v2737_pb_checked : Scalar.distance (sourceCoefficient 34 35 1 1) v2737_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2737_pg : Scalar.QComplex := ((-93086407496100230562051 : Int)/10^30,(64549397891556357351 : Int)/10^30)
theorem v2737_pg_checked : Scalar.distance (sourceCoefficient 34 35 1 2) v2737_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2737_mb : Scalar.QComplex := ((-671547124674639339996436 : Int)/10^30,(-431476998216145857758396049 : Int)/10^30)
theorem v2737_mb_checked : Scalar.distance (sourceCoefficient 34 35 3 1) v2737_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2737_mg : Scalar.QComplex := ((-93086317132553277324380 : Int)/10^30,(144878751069837631984 : Int)/10^30)
theorem v2737_mg_checked : Scalar.distance (sourceCoefficient 34 35 3 2) v2737_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2737_upper : Scalar.QComplex := ((999997073385601702631070629032 : Int)/10^30,(-2419342933840281671545295887 : Int)/10^30)
theorem v2737_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 35 5) 1) 14) v2737_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2737 : Material (34 : Basis) (35 : Basis) where
  plus := ![v2737_pa,v2737_pb,v2737_pg]
  minus := ![(Primitive.Addresses.material2737 1).one,v2737_mb,v2737_mg]
  upper := v2737_upper
  lower := (Primitive.Addresses.material2737 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2737_pa_checked.trans (by decide +kernel)
    · exact v2737_pb_checked.trans (by decide +kernel)
    · exact v2737_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 35 Primitive.Addresses.material2737
    · exact v2737_mb_checked.trans (by decide +kernel)
    · exact v2737_mg_checked.trans (by decide +kernel)
  upper_error := v2737_upper_checked
  lower_error := reuse_lower_error 34 35 Primitive.Addresses.material2737

def v2738_pa : Scalar.QComplex := ((999999748248065045133320130729 : Int)/10^30,(-709580021231359505234428872 : Int)/10^30)
theorem v2738_pa_checked : Scalar.distance (sourceCoefficient 34 36 1 0) v2738_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2738_pb : Scalar.QComplex := ((-306167828279952874163935 : Int)/10^30,(-431477412047630471807316897 : Int)/10^30)
theorem v2738_pb_checked : Scalar.distance (sourceCoefficient 34 36 1 1) v2738_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2738_pg : Scalar.QComplex := ((-93086406426936099974982 : Int)/10^30,(66052270877563279310 : Int)/10^30)
theorem v2738_pg_checked : Scalar.distance (sourceCoefficient 34 36 1 2) v2738_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2738_mb : Scalar.QComplex := ((-678513287855531974390259 : Int)/10^30,(-431476987179823956085251383 : Int)/10^30)
theorem v2738_mb_checked : Scalar.distance (sourceCoefficient 34 36 3 1) v2738_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2738_mg : Scalar.QComplex := ((-93086314766477844798641 : Int)/10^30,(146381622573615765233 : Int)/10^30)
theorem v2738_mg_checked : Scalar.distance (sourceCoefficient 34 36 3 2) v2738_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2738_upper : Scalar.QComplex := ((999997034195164203110670945183 : Int)/10^30,(-2435487810602930244502524128 : Int)/10^30)
theorem v2738_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 36 5) 1) 14) v2738_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2738 : Material (34 : Basis) (36 : Basis) where
  plus := ![v2738_pa,v2738_pb,v2738_pg]
  minus := ![(Primitive.Addresses.material2738 1).one,v2738_mb,v2738_mg]
  upper := v2738_upper
  lower := (Primitive.Addresses.material2738 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2738_pa_checked.trans (by decide +kernel)
    · exact v2738_pb_checked.trans (by decide +kernel)
    · exact v2738_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 36 Primitive.Addresses.material2738
    · exact v2738_mb_checked.trans (by decide +kernel)
    · exact v2738_mg_checked.trans (by decide +kernel)
  upper_error := v2738_upper_checked
  lower_error := reuse_lower_error 34 36 Primitive.Addresses.material2738

def v2739_pa : Scalar.QComplex := ((999999743332416050391834831280 : Int)/10^30,(-716474076307697039211232221 : Int)/10^30)
theorem v2739_pa_checked : Scalar.distance (sourceCoefficient 34 37 1 0) v2739_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2739_pb : Scalar.QComplex := ((-309142458021266785826342 : Int)/10^30,(-431477409856284413234402854 : Int)/10^30)
theorem v2739_pb_checked : Scalar.distance (sourceCoefficient 34 37 1 1) v2739_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2739_pg : Scalar.QComplex := ((-93086405961766840017033 : Int)/10^30,(66694013846451597404 : Int)/10^30)
theorem v2739_pg_checked : Scalar.distance (sourceCoefficient 34 37 1 2) v2739_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2739_mb : Scalar.QComplex := ((-681487914598222332080725 : Int)/10^30,(-431476982421507219046980010 : Int)/10^30)
theorem v2739_mb_checked : Scalar.distance (sourceCoefficient 34 37 3 1) v2739_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2739_mg : Scalar.QComplex := ((-93086313747513478924237 : Int)/10^30,(147023364902133726009 : Int)/10^30)
theorem v2739_mg_checked : Scalar.distance (sourceCoefficient 34 37 3 2) v2739_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2739_upper : Scalar.QComplex := ((999997017381008891683329772497 : Int)/10^30,(-2442381846927418354140948875 : Int)/10^30)
theorem v2739_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 37 5) 1) 14) v2739_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2739 : Material (34 : Basis) (37 : Basis) where
  plus := ![v2739_pa,v2739_pb,v2739_pg]
  minus := ![(Primitive.Addresses.material2739 1).one,v2739_mb,v2739_mg]
  upper := v2739_upper
  lower := (Primitive.Addresses.material2739 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2739_pa_checked.trans (by decide +kernel)
    · exact v2739_pb_checked.trans (by decide +kernel)
    · exact v2739_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 37 Primitive.Addresses.material2739
    · exact v2739_mb_checked.trans (by decide +kernel)
    · exact v2739_mg_checked.trans (by decide +kernel)
  upper_error := v2739_upper_checked
  lower_error := reuse_lower_error 34 37 Primitive.Addresses.material2739

def v2740_pa : Scalar.QComplex := ((999999726366373525148967509738 : Int)/10^30,(-739775086140605661855486130 : Int)/10^30)
theorem v2740_pa_checked : Scalar.distance (sourceCoefficient 34 38 1 0) v2740_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2740_pb : Scalar.QComplex := ((-319196319758167397478439 : Int)/10^30,(-431477402247434835763396485 : Int)/10^30)
theorem v2740_pb_checked : Scalar.distance (sourceCoefficient 34 38 1 1) v2740_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2740_pg : Scalar.QComplex := ((-93086404351350749681806 : Int)/10^30,(68863021640778092138 : Int)/10^30)
theorem v2740_pg_checked : Scalar.distance (sourceCoefficient 34 38 1 2) v2740_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2740_mb : Scalar.QComplex := ((-691541766025516239410614 : Int)/10^30,(-431476966136630604876750302 : Int)/10^30)
theorem v2740_mb_checked : Scalar.distance (sourceCoefficient 34 38 3 1) v2740_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2740_mg : Scalar.QComplex := ((-93086310265341950201444 : Int)/10^30,(149192370499122934851 : Int)/10^30)
theorem v2740_mg_checked : Scalar.distance (sourceCoefficient 34 38 3 2) v2740_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2740_upper : Scalar.QComplex := ((999996960199562514867092622582 : Int)/10^30,(-2465682792774359708341142036 : Int)/10^30)
theorem v2740_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 38 5) 1) 14) v2740_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2740 : Material (34 : Basis) (38 : Basis) where
  plus := ![v2740_pa,v2740_pb,v2740_pg]
  minus := ![(Primitive.Addresses.material2740 1).one,v2740_mb,v2740_mg]
  upper := v2740_upper
  lower := (Primitive.Addresses.material2740 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2740_pa_checked.trans (by decide +kernel)
    · exact v2740_pb_checked.trans (by decide +kernel)
    · exact v2740_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 38 Primitive.Addresses.material2740
    · exact v2740_mb_checked.trans (by decide +kernel)
    · exact v2740_mg_checked.trans (by decide +kernel)
  upper_error := v2740_upper_checked
  lower_error := reuse_lower_error 34 38 Primitive.Addresses.material2740

def v2741_pa : Scalar.QComplex := ((999999716275182501172380021749 : Int)/10^30,(-753292476066157968109777369 : Int)/10^30)
theorem v2741_pa_checked : Scalar.distance (sourceCoefficient 34 39 1 0) v2741_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2741_pb : Scalar.QComplex := ((-325028769491380469037404 : Int)/10^30,(-431477397690225297445411310 : Int)/10^30)
theorem v2741_pb_checked : Scalar.distance (sourceCoefficient 34 39 1 1) v2741_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2741_pg : Scalar.QComplex := ((-93086403390090885514168 : Int)/10^30,(70121307192969850426 : Int)/10^30)
theorem v2741_pg_checked : Scalar.distance (sourceCoefficient 34 39 1 2) v2741_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2741_mb : Scalar.QComplex := ((-697374209654375136703386 : Int)/10^30,(-431476956546281327437973718 : Int)/10^30)
theorem v2741_mb_checked : Scalar.distance (sourceCoefficient 34 39 3 1) v2741_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2741_mg : Scalar.QComplex := ((-93086308218238683490839 : Int)/10^30,(150450654753273506327 : Int)/10^30)
theorem v2741_mg_checked : Scalar.distance (sourceCoefficient 34 39 3 2) v2741_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2741_upper : Scalar.QComplex := ((999996926778597797065669856085 : Int)/10^30,(-2479200145150867342962181797 : Int)/10^30)
theorem v2741_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 39 5) 1) 14) v2741_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2741 : Material (34 : Basis) (39 : Basis) where
  plus := ![v2741_pa,v2741_pb,v2741_pg]
  minus := ![(Primitive.Addresses.material2741 1).one,v2741_mb,v2741_mg]
  upper := v2741_upper
  lower := (Primitive.Addresses.material2741 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2741_pa_checked.trans (by decide +kernel)
    · exact v2741_pb_checked.trans (by decide +kernel)
    · exact v2741_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 39 Primitive.Addresses.material2741
    · exact v2741_mb_checked.trans (by decide +kernel)
    · exact v2741_mg_checked.trans (by decide +kernel)
  upper_error := v2741_upper_checked
  lower_error := reuse_lower_error 34 39 Primitive.Addresses.material2741

def v2742_pa : Scalar.QComplex := ((999999698890251055263132521305 : Int)/10^30,(-776027968067126318693722104 : Int)/10^30)
theorem v2742_pa_checked : Scalar.distance (sourceCoefficient 34 40 1 0) v2742_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2742_pb : Scalar.QComplex := ((-334838622887389927518031 : Int)/10^30,(-431477389788163877256766780 : Int)/10^30)
theorem v2742_pb_checked : Scalar.distance (sourceCoefficient 34 40 1 1) v2742_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2742_pg : Scalar.QComplex := ((-93086401728549776975676 : Int)/10^30,(72237672939554281663 : Int)/10^30)
theorem v2742_pg_checked : Scalar.distance (sourceCoefficient 34 40 1 2) v2742_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2742_mb : Scalar.QComplex := ((-707184052578604733413519 : Int)/10^30,(-431476940178761188187624655 : Int)/10^30)
theorem v2742_mb_checked : Scalar.distance (sourceCoefficient 34 40 3 1) v2742_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2742_mg : Scalar.QComplex := ((-93086304730369871892545 : Int)/10^30,(152567018278003103784 : Int)/10^30)
theorem v2742_mg_checked : Scalar.distance (sourceCoefficient 34 40 3 2) v2742_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2742_upper : Scalar.QComplex := ((999996870154295598020849652988 : Int)/10^30,(-2501935573285176529621941615 : Int)/10^30)
theorem v2742_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 40 5) 1) 14) v2742_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2742 : Material (34 : Basis) (40 : Basis) where
  plus := ![v2742_pa,v2742_pb,v2742_pg]
  minus := ![(Primitive.Addresses.material2742 1).one,v2742_mb,v2742_mg]
  upper := v2742_upper
  lower := (Primitive.Addresses.material2742 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2742_pa_checked.trans (by decide +kernel)
    · exact v2742_pb_checked.trans (by decide +kernel)
    · exact v2742_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 40 Primitive.Addresses.material2742
    · exact v2742_mb_checked.trans (by decide +kernel)
    · exact v2742_mg_checked.trans (by decide +kernel)
  upper_error := v2742_upper_checked
  lower_error := reuse_lower_error 34 40 Primitive.Addresses.material2742

def v2743_pa : Scalar.QComplex := ((999999687545373330021332339659 : Int)/10^30,(-790511957981701632807306894 : Int)/10^30)
theorem v2743_pa_checked : Scalar.distance (sourceCoefficient 34 41 1 0) v2743_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2743_pb : Scalar.QComplex := ((-341088138698719801586706 : Int)/10^30,(-431477384598966552937383725 : Int)/10^30)
theorem v2743_pb_checked : Scalar.distance (sourceCoefficient 34 41 1 1) v2743_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2743_pg : Scalar.QComplex := ((-93086400640767169296683 : Int)/10^30,(73585935824268086616 : Int)/10^30)
theorem v2743_pg_checked : Scalar.distance (sourceCoefficient 34 41 1 2) v2743_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2743_mb : Scalar.QComplex := ((-713433561584910675825773 : Int)/10^30,(-431476929596515118609450673 : Int)/10^30)
theorem v2743_mb_checked : Scalar.distance (sourceCoefficient 34 41 3 1) v2743_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2743_mg : Scalar.QComplex := ((-93086302479097523242882 : Int)/10^30,(153915279721989619583 : Int)/10^30)
theorem v2743_mg_checked : Scalar.distance (sourceCoefficient 34 41 3 2) v2743_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2743_upper : Scalar.QComplex := ((999996833811382154385588989637 : Int)/10^30,(-2516419522047320520448647079 : Int)/10^30)
theorem v2743_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 41 5) 1) 14) v2743_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2743 : Material (34 : Basis) (41 : Basis) where
  plus := ![v2743_pa,v2743_pb,v2743_pg]
  minus := ![(Primitive.Addresses.material2743 1).one,v2743_mb,v2743_mg]
  upper := v2743_upper
  lower := (Primitive.Addresses.material2743 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2743_pa_checked.trans (by decide +kernel)
    · exact v2743_pb_checked.trans (by decide +kernel)
    · exact v2743_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 41 Primitive.Addresses.material2743
    · exact v2743_mb_checked.trans (by decide +kernel)
    · exact v2743_mg_checked.trans (by decide +kernel)
  upper_error := v2743_upper_checked
  lower_error := reuse_lower_error 34 41 Primitive.Addresses.material2743

def v2744_pa : Scalar.QComplex := ((999999678241054519306444908779 : Int)/10^30,(-802195604221668689975380623 : Int)/10^30)
theorem v2744_pa_checked : Scalar.distance (sourceCoefficient 34 42 1 0) v2744_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2744_pb : Scalar.QComplex := ((-346129369188102856799258 : Int)/10^30,(-431477380325107093564855911 : Int)/10^30)
theorem v2744_pb_checked : Scalar.distance (sourceCoefficient 34 42 1 1) v2744_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2744_pg : Scalar.QComplex := ((-93086399746695666562322 : Int)/10^30,(74673524716494885634 : Int)/10^30)
theorem v2744_pg_checked : Scalar.distance (sourceCoefficient 34 42 1 2) v2744_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2744_mb : Scalar.QComplex := ((-718474786509064998271962 : Int)/10^30,(-431476920972302386845349827 : Int)/10^30)
theorem v2744_mb_checked : Scalar.distance (sourceCoefficient 34 42 3 1) v2744_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2744_mg : Scalar.QComplex := ((-93086300646486122605840 : Int)/10^30,(155002867437713929383 : Int)/10^30)
theorem v2744_mg_checked : Scalar.distance (sourceCoefficient 34 42 3 2) v2744_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2744_upper : Scalar.QComplex := ((999996804342163723284621951467 : Int)/10^30,(-2528103134827458774598028320 : Int)/10^30)
theorem v2744_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 42 5) 1) 14) v2744_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2744 : Material (34 : Basis) (42 : Basis) where
  plus := ![v2744_pa,v2744_pb,v2744_pg]
  minus := ![(Primitive.Addresses.material2744 1).one,v2744_mb,v2744_mg]
  upper := v2744_upper
  lower := (Primitive.Addresses.material2744 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2744_pa_checked.trans (by decide +kernel)
    · exact v2744_pb_checked.trans (by decide +kernel)
    · exact v2744_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 42 Primitive.Addresses.material2744
    · exact v2744_mb_checked.trans (by decide +kernel)
    · exact v2744_mg_checked.trans (by decide +kernel)
  upper_error := v2744_upper_checked
  lower_error := reuse_lower_error 34 42 Primitive.Addresses.material2744

def v2745_pa : Scalar.QComplex := ((999999665705059694855695106797 : Int)/10^30,(-817673387641533492122109586 : Int)/10^30)
theorem v2745_pa_checked : Scalar.distance (sourceCoefficient 34 43 1 0) v2745_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2745_pb : Scalar.QComplex := ((-352807684474607087404290 : Int)/10^30,(-431477374542429714552324481 : Int)/10^30)
theorem v2745_pb_checked : Scalar.distance (sourceCoefficient 34 43 1 1) v2745_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2745_pg : Scalar.QComplex := ((-93086398539456311098893 : Int)/10^30,(76114296281731269228 : Int)/10^30)
theorem v2745_pg_checked : Scalar.distance (sourceCoefficient 34 43 1 2) v2745_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2745_mb : Scalar.QComplex := ((-725153094318737097658264 : Int)/10^30,(-431476909426541848889756961 : Int)/10^30)
theorem v2745_mb_checked : Scalar.distance (sourceCoefficient 34 43 3 1) v2745_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2745_mg : Scalar.QComplex := ((-93086298195926245796268 : Int)/10^30,(156443637424692021003 : Int)/10^30)
theorem v2745_mg_checked : Scalar.distance (sourceCoefficient 34 43 3 2) v2745_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2745_upper : Scalar.QComplex := ((999996765092937520582294095505 : Int)/10^30,(-2543580873558993510579293249 : Int)/10^30)
theorem v2745_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 43 5) 1) 14) v2745_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2745 : Material (34 : Basis) (43 : Basis) where
  plus := ![v2745_pa,v2745_pb,v2745_pg]
  minus := ![(Primitive.Addresses.material2745 1).one,v2745_mb,v2745_mg]
  upper := v2745_upper
  lower := (Primitive.Addresses.material2745 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2745_pa_checked.trans (by decide +kernel)
    · exact v2745_pb_checked.trans (by decide +kernel)
    · exact v2745_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 43 Primitive.Addresses.material2745
    · exact v2745_mb_checked.trans (by decide +kernel)
    · exact v2745_mg_checked.trans (by decide +kernel)
  upper_error := v2745_upper_checked
  lower_error := reuse_lower_error 34 43 Primitive.Addresses.material2745

def v2746_pa : Scalar.QComplex := ((999999660899799624174204388960 : Int)/10^30,(-823529165095387314721134411 : Int)/10^30)
theorem v2746_pa_checked : Scalar.distance (sourceCoefficient 34 44 1 0) v2746_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2746_pb : Scalar.QComplex := ((-355334320677117602491642 : Int)/10^30,(-431477372318709310756117531 : Int)/10^30)
theorem v2746_pb_checked : Scalar.distance (sourceCoefficient 34 44 1 1) v2746_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2746_pg : Scalar.QComplex := ((-93086398075932705907996 : Int)/10^30,(76659389684424132119 : Int)/10^30)
theorem v2746_pg_checked : Scalar.distance (sourceCoefficient 34 44 1 2) v2746_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2746_mb : Scalar.QComplex := ((-727679727661494925745035 : Int)/10^30,(-431476905022449025789985519 : Int)/10^30)
theorem v2746_mb_checked : Scalar.distance (sourceCoefficient 34 44 3 1) v2746_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2746_mg : Scalar.QComplex := ((-93086297262011756767968 : Int)/10^30,(156988730224421703121 : Int)/10^30)
theorem v2746_mg_checked : Scalar.distance (sourceCoefficient 34 44 3 2) v2746_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2746_upper : Scalar.QComplex := ((999996750181143953400372468682 : Int)/10^30,(-2549436633997911731394928923 : Int)/10^30)
theorem v2746_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 44 5) 1) 14) v2746_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2746 : Material (34 : Basis) (44 : Basis) where
  plus := ![v2746_pa,v2746_pb,v2746_pg]
  minus := ![(Primitive.Addresses.material2746 1).one,v2746_mb,v2746_mg]
  upper := v2746_upper
  lower := (Primitive.Addresses.material2746 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2746_pa_checked.trans (by decide +kernel)
    · exact v2746_pb_checked.trans (by decide +kernel)
    · exact v2746_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 44 Primitive.Addresses.material2746
    · exact v2746_mb_checked.trans (by decide +kernel)
    · exact v2746_mg_checked.trans (by decide +kernel)
  upper_error := v2746_upper_checked
  lower_error := reuse_lower_error 34 44 Primitive.Addresses.material2746

def v2747_pa : Scalar.QComplex := ((999999658496349077254111263728 : Int)/10^30,(-826442487545714329066228616 : Int)/10^30)
theorem v2747_pa_checked : Scalar.distance (sourceCoefficient 34 45 1 0) v2747_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2747_pb : Scalar.QComplex := ((-356591353755621345545052 : Int)/10^30,(-431477371205031919397839815 : Int)/10^30)
theorem v2747_pb_checked : Scalar.distance (sourceCoefficient 34 45 1 1) v2747_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2747_pg : Scalar.QComplex := ((-93086397843936694956619 : Int)/10^30,(76930580462887156877 : Int)/10^30)
theorem v2747_pg_checked : Scalar.distance (sourceCoefficient 34 45 1 2) v2747_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2747_mb : Scalar.QComplex := ((-728936759310894373847317 : Int)/10^30,(-431476902824009117024188458 : Int)/10^30)
theorem v2747_mb_checked : Scalar.distance (sourceCoefficient 34 45 3 1) v2747_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2747_mg : Scalar.QComplex := ((-93086296795990404364976 : Int)/10^30,(157259920701705898288 : Int)/10^30)
theorem v2747_mg_checked : Scalar.distance (sourceCoefficient 34 45 3 2) v2747_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2747_upper : Scalar.QComplex := ((999996742749566731421251043698 : Int)/10^30,(-2552349947961049574219103945 : Int)/10^30)
theorem v2747_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 45 5) 1) 14) v2747_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2747 : Material (34 : Basis) (45 : Basis) where
  plus := ![v2747_pa,v2747_pb,v2747_pg]
  minus := ![(Primitive.Addresses.material2747 1).one,v2747_mb,v2747_mg]
  upper := v2747_upper
  lower := (Primitive.Addresses.material2747 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2747_pa_checked.trans (by decide +kernel)
    · exact v2747_pb_checked.trans (by decide +kernel)
    · exact v2747_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 45 Primitive.Addresses.material2747
    · exact v2747_mb_checked.trans (by decide +kernel)
    · exact v2747_mg_checked.trans (by decide +kernel)
  upper_error := v2747_upper_checked
  lower_error := reuse_lower_error 34 45 Primitive.Addresses.material2747

def v2748_pa : Scalar.QComplex := ((999999644838349007861782766135 : Int)/10^30,(-842806725082612341518461580 : Int)/10^30)
theorem v2748_pa_checked : Scalar.distance (sourceCoefficient 34 46 1 0) v2748_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2748_pb : Scalar.QComplex := ((-363652153979154606850634 : Int)/10^30,(-431477364858722333217765183 : Int)/10^30)
theorem v2748_pb_checked : Scalar.distance (sourceCoefficient 34 46 1 1) v2748_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2748_pg : Scalar.QComplex := ((-93086396523676948555839 : Int)/10^30,(78453868867667232912 : Int)/10^30)
theorem v2748_pg_checked : Scalar.distance (sourceCoefficient 34 46 1 2) v2748_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2748_mb : Scalar.QComplex := ((-735997551428789671719772 : Int)/10^30,(-431476890384549307593115603 : Int)/10^30)
theorem v2748_mb_checked : Scalar.distance (sourceCoefficient 34 46 3 1) v2748_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2748_mg : Scalar.QComplex := ((-93086294161201862594996 : Int)/10^30,(158783207399971384652 : Int)/10^30)
theorem v2748_mg_checked : Scalar.distance (sourceCoefficient 34 46 3 2) v2748_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2748_upper : Scalar.QComplex := ((999996700848397567362338339517 : Int)/10^30,(-2568714137552868978151777312 : Int)/10^30)
theorem v2748_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 46 5) 1) 14) v2748_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2748 : Material (34 : Basis) (46 : Basis) where
  plus := ![v2748_pa,v2748_pb,v2748_pg]
  minus := ![(Primitive.Addresses.material2748 1).one,v2748_mb,v2748_mg]
  upper := v2748_upper
  lower := (Primitive.Addresses.material2748 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2748_pa_checked.trans (by decide +kernel)
    · exact v2748_pb_checked.trans (by decide +kernel)
    · exact v2748_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 46 Primitive.Addresses.material2748
    · exact v2748_mb_checked.trans (by decide +kernel)
    · exact v2748_mg_checked.trans (by decide +kernel)
  upper_error := v2748_upper_checked
  lower_error := reuse_lower_error 34 46 Primitive.Addresses.material2748

def v2749_pa : Scalar.QComplex := ((999999641511586046270941380390 : Int)/10^30,(-846744766380941487882725212 : Int)/10^30)
theorem v2749_pa_checked : Scalar.distance (sourceCoefficient 34 47 1 0) v2749_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2749_pb : Scalar.QComplex := ((-365351330167530567173527 : Int)/10^30,(-431477363308489645584462298 : Int)/10^30)
theorem v2749_pb_checked : Scalar.distance (sourceCoefficient 34 47 1 1) v2749_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2749_pg : Scalar.QComplex := ((-93086396201616058008537 : Int)/10^30,(78820447061198202224 : Int)/10^30)
theorem v2749_pg_checked : Scalar.distance (sourceCoefficient 34 47 1 2) v2749_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2749_mb : Scalar.QComplex := ((-737696725646703691383067 : Int)/10^30,(-431476887368004674668507228 : Int)/10^30)
theorem v2749_mb_checked : Scalar.distance (sourceCoefficient 34 47 3 1) v2749_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2749_mg : Scalar.QComplex := ((-93086293522800621017410 : Int)/10^30,(159149785179084495602 : Int)/10^30)
theorem v2749_mg_checked : Scalar.distance (sourceCoefficient 34 47 3 2) v2749_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2749_upper : Scalar.QComplex := ((999996690724937535993883821387 : Int)/10^30,(-2572652167244257135353732116 : Int)/10^30)
theorem v2749_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 47 5) 1) 14) v2749_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2749 : Material (34 : Basis) (47 : Basis) where
  plus := ![v2749_pa,v2749_pb,v2749_pg]
  minus := ![(Primitive.Addresses.material2749 1).one,v2749_mb,v2749_mg]
  upper := v2749_upper
  lower := (Primitive.Addresses.material2749 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2749_pa_checked.trans (by decide +kernel)
    · exact v2749_pb_checked.trans (by decide +kernel)
    · exact v2749_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 47 Primitive.Addresses.material2749
    · exact v2749_mb_checked.trans (by decide +kernel)
    · exact v2749_mg_checked.trans (by decide +kernel)
  upper_error := v2749_upper_checked
  lower_error := reuse_lower_error 34 47 Primitive.Addresses.material2749

def v2750_pa : Scalar.QComplex := ((999999617908678415391366389747 : Int)/10^30,(-874175324048579649078115266 : Int)/10^30)
theorem v2750_pa_checked : Scalar.distance (sourceCoefficient 34 48 1 0) v2750_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2750_pb : Scalar.QComplex := ((-377186998353817403141320 : Int)/10^30,(-431477352262779839392431521 : Int)/10^30)
theorem v2750_pb_checked : Scalar.distance (sourceCoefficient 34 48 1 1) v2750_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2750_pg : Scalar.QComplex := ((-93086393911566928778959 : Int)/10^30,(81373859654403329455 : Int)/10^30)
theorem v2750_pg_checked : Scalar.distance (sourceCoefficient 34 48 1 2) v2750_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2750_mb : Scalar.QComplex := ((-749532379894080262396939 : Int)/10^30,(-431476866108650395240552739 : Int)/10^30)
theorem v2750_mb_checked : Scalar.distance (sourceCoefficient 34 48 3 1) v2750_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2750_mg : Scalar.QComplex := ((-93086289029272277975902 : Int)/10^30,(161703194845328159121 : Int)/10^30)
theorem v2750_mg_checked : Scalar.distance (sourceCoefficient 34 48 3 2) v2750_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2750_upper : Scalar.QComplex := ((999996619779411005281829780517 : Int)/10^30,(-2600082643320824538409992421 : Int)/10^30)
theorem v2750_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 48 5) 1) 14) v2750_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2750 : Material (34 : Basis) (48 : Basis) where
  plus := ![v2750_pa,v2750_pb,v2750_pg]
  minus := ![(Primitive.Addresses.material2750 1).one,v2750_mb,v2750_mg]
  upper := v2750_upper
  lower := (Primitive.Addresses.material2750 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2750_pa_checked.trans (by decide +kernel)
    · exact v2750_pb_checked.trans (by decide +kernel)
    · exact v2750_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 48 Primitive.Addresses.material2750
    · exact v2750_mb_checked.trans (by decide +kernel)
    · exact v2750_mg_checked.trans (by decide +kernel)
  upper_error := v2750_upper_checked
  lower_error := reuse_lower_error 34 48 Primitive.Addresses.material2750

def v2751_pa : Scalar.QComplex := ((999999598400421791608786279038 : Int)/10^30,(-896213699479404973397066916 : Int)/10^30)
theorem v2751_pa_checked : Scalar.distance (sourceCoefficient 34 49 1 0) v2751_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2751_pb : Scalar.QComplex := ((-386696061175573624663288 : Int)/10^30,(-431477343074786204008325081 : Int)/10^30)
theorem v2751_pb_checked : Scalar.distance (sourceCoefficient 34 49 1 1) v2751_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2751_pg : Scalar.QComplex := ((-93086392012486722757198 : Int)/10^30,(83425333260279508500 : Int)/10^30)
theorem v2751_pg_checked : Scalar.distance (sourceCoefficient 34 49 1 2) v2751_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2751_mb : Scalar.QComplex := ((-759041431246353114274580 : Int)/10^30,(-431476848714767238082046778 : Int)/10^30)
theorem v2751_mb_checked : Scalar.distance (sourceCoefficient 34 49 3 1) v2751_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2751_mg : Scalar.QComplex := ((-93086285359863452138699 : Int)/10^30,(163754666048526271324 : Int)/10^30)
theorem v2751_mg_checked : Scalar.distance (sourceCoefficient 34 49 3 2) v2751_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2751_upper : Scalar.QComplex := ((999996562234946748952744848746 : Int)/10^30,(-2622120952258597310514123233 : Int)/10^30)
theorem v2751_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 49 5) 1) 14) v2751_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2751 : Material (34 : Basis) (49 : Basis) where
  plus := ![v2751_pa,v2751_pb,v2751_pg]
  minus := ![(Primitive.Addresses.material2751 1).one,v2751_mb,v2751_mg]
  upper := v2751_upper
  lower := (Primitive.Addresses.material2751 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2751_pa_checked.trans (by decide +kernel)
    · exact v2751_pb_checked.trans (by decide +kernel)
    · exact v2751_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 49 Primitive.Addresses.material2751
    · exact v2751_mb_checked.trans (by decide +kernel)
    · exact v2751_mg_checked.trans (by decide +kernel)
  upper_error := v2751_upper_checked
  lower_error := reuse_lower_error 34 49 Primitive.Addresses.material2751

def v2752_pa : Scalar.QComplex := ((999999596089103554534170047456 : Int)/10^30,(-898788979542428186155494664 : Int)/10^30)
theorem v2752_pa_checked : Scalar.distance (sourceCoefficient 34 50 1 0) v2752_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2752_pb : Scalar.QComplex := ((-387807236536054743582100 : Int)/10^30,(-431477341982895758545392675 : Int)/10^30)
theorem v2752_pb_checked : Scalar.distance (sourceCoefficient 34 50 1 1) v2752_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2752_pg : Scalar.QComplex := ((-93086391787128990172384 : Int)/10^30,(83665056876868457368 : Int)/10^30)
theorem v2752_pg_checked : Scalar.distance (sourceCoefficient 34 50 1 2) v2752_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2752_mb : Scalar.QComplex := ((-760152605250840585749176 : Int)/10^30,(-431476846663982908565083959 : Int)/10^30)
theorem v2752_mb_checked : Scalar.distance (sourceCoefficient 34 50 3 1) v2752_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2752_mg : Scalar.QComplex := ((-93086284927635119099502 : Int)/10^30,(163994389381381588341 : Int)/10^30)
theorem v2752_mg_checked : Scalar.distance (sourceCoefficient 34 50 3 2) v2752_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2752_upper : Scalar.QComplex := ((999996555478932193119389952109 : Int)/10^30,(-2624696224496917787007843447 : Int)/10^30)
theorem v2752_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 50 5) 1) 14) v2752_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2752 : Material (34 : Basis) (50 : Basis) where
  plus := ![v2752_pa,v2752_pb,v2752_pg]
  minus := ![(Primitive.Addresses.material2752 1).one,v2752_mb,v2752_mg]
  upper := v2752_upper
  lower := (Primitive.Addresses.material2752 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2752_pa_checked.trans (by decide +kernel)
    · exact v2752_pb_checked.trans (by decide +kernel)
    · exact v2752_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 50 Primitive.Addresses.material2752
    · exact v2752_mb_checked.trans (by decide +kernel)
    · exact v2752_mg_checked.trans (by decide +kernel)
  upper_error := v2752_upper_checked
  lower_error := reuse_lower_error 34 50 Primitive.Addresses.material2752

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
