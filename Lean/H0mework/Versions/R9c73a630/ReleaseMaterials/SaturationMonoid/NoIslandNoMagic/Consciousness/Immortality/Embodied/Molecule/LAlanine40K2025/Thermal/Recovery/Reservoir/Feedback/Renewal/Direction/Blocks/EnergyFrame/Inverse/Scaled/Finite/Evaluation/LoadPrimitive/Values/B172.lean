import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B114
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B115

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2753_pa : Scalar.QComplex := ((999999585869625212895273632826 : Int)/10^30,(-910088225432151237996606450 : Int)/10^30)
theorem v2753_pa_checked : Scalar.distance (sourceCoefficient 34 51 1 0) v2753_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2753_pb : Scalar.QComplex := ((-392682606700138384171771 : Int)/10^30,(-431477337147043995268311967 : Int)/10^30)
theorem v2753_pb_checked : Scalar.distance (sourceCoefficient 34 51 1 1) v2753_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2753_pg : Scalar.QComplex := ((-93086390789841256413441 : Int)/10^30,(84716863289636721027 : Int)/10^30)
theorem v2753_pg_checked : Scalar.distance (sourceCoefficient 34 51 1 2) v2753_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2753_mb : Scalar.QComplex := ((-765027969426478825796934 : Int)/10^30,(-431476837620908072813494712 : Int)/10^30)
theorem v2753_mb_checked : Scalar.distance (sourceCoefficient 34 51 3 1) v2753_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2753_mg : Scalar.QComplex := ((-93086283022686194059664 : Int)/10^30,(165046194541899856536 : Int)/10^30)
theorem v2753_mg_checked : Scalar.distance (sourceCoefficient 34 51 3 2) v2753_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2753_upper : Scalar.QComplex := ((999996525757995726110821343947 : Int)/10^30,(-2635995435919848874930883487 : Int)/10^30)
theorem v2753_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 51 5) 1) 14) v2753_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2753 : Material (34 : Basis) (51 : Basis) where
  plus := ![v2753_pa,v2753_pb,v2753_pg]
  minus := ![(Primitive.Addresses.material2753 1).one,v2753_mb,v2753_mg]
  upper := v2753_upper
  lower := (Primitive.Addresses.material2753 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2753_pa_checked.trans (by decide +kernel)
    · exact v2753_pb_checked.trans (by decide +kernel)
    · exact v2753_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 51 Primitive.Addresses.material2753
    · exact v2753_mb_checked.trans (by decide +kernel)
    · exact v2753_mg_checked.trans (by decide +kernel)
  upper_error := v2753_upper_checked
  lower_error := reuse_lower_error 34 51 Primitive.Addresses.material2753

def v2754_pa : Scalar.QComplex := ((999999563563010816807429762191 : Int)/10^30,(-934277147258317355652252434 : Int)/10^30)
theorem v2754_pa_checked : Scalar.distance (sourceCoefficient 34 52 1 0) v2754_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2754_pb : Scalar.QComplex := ((-403119581689966165952277 : Int)/10^30,(-431477326547741802334467277 : Int)/10^30)
theorem v2754_pb_checked : Scalar.distance (sourceCoefficient 34 52 1 1) v2754_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2754_pg : Scalar.QComplex := ((-93086388608279496655663 : Int)/10^30,(86968523553803071996 : Int)/10^30)
theorem v2754_pg_checked : Scalar.distance (sourceCoefficient 34 52 1 2) v2754_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2754_mb : Scalar.QComplex := ((-775464931383423407891448 : Int)/10^30,(-431476818014970474166842318 : Int)/10^30)
theorem v2754_mb_checked : Scalar.distance (sourceCoefficient 34 52 3 1) v2754_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2754_mg : Scalar.QComplex := ((-93086278898043849635215 : Int)/10^30,(167297852085080640422 : Int)/10^30)
theorem v2754_mg_checked : Scalar.distance (sourceCoefficient 34 52 3 2) v2754_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2754_upper : Scalar.QComplex := ((999996461703529882988425655110 : Int)/10^30,(-2660184283220264555471979278 : Int)/10^30)
theorem v2754_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 52 5) 1) 14) v2754_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2754 : Material (34 : Basis) (52 : Basis) where
  plus := ![v2754_pa,v2754_pb,v2754_pg]
  minus := ![(Primitive.Addresses.material2754 1).one,v2754_mb,v2754_mg]
  upper := v2754_upper
  lower := (Primitive.Addresses.material2754 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2754_pa_checked.trans (by decide +kernel)
    · exact v2754_pb_checked.trans (by decide +kernel)
    · exact v2754_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 52 Primitive.Addresses.material2754
    · exact v2754_mb_checked.trans (by decide +kernel)
    · exact v2754_mg_checked.trans (by decide +kernel)
  upper_error := v2754_upper_checked
  lower_error := reuse_lower_error 34 52 Primitive.Addresses.material2754

def v2755_pa : Scalar.QComplex := ((999999560096817327460650257257 : Int)/10^30,(-937979835513679139377284748 : Int)/10^30)
theorem v2755_pa_checked : Scalar.distance (sourceCoefficient 34 53 1 0) v2755_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2755_pb : Scalar.QComplex := ((-404717208269807879151774 : Int)/10^30,(-431477324895560231319003360 : Int)/10^30)
theorem v2755_pb_checked : Scalar.distance (sourceCoefficient 34 53 1 1) v2755_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2755_pg : Scalar.QComplex := ((-93086388268731897715396 : Int)/10^30,(87313193566219355975 : Int)/10^30)
theorem v2755_pg_checked : Scalar.distance (sourceCoefficient 34 53 1 2) v2755_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2755_mb : Scalar.QComplex := ((-777062555942637445983484 : Int)/10^30,(-431476814984109734360769299 : Int)/10^30)
theorem v2755_mb_checked : Scalar.distance (sourceCoefficient 34 53 3 1) v2755_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2755_mg : Scalar.QComplex := ((-93086278261061679769889 : Int)/10^30,(167642521676146241351 : Int)/10^30)
theorem v2755_mg_checked : Scalar.distance (sourceCoefficient 34 53 3 2) v2755_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2755_upper : Scalar.QComplex := ((999996451846837532629820703858 : Int)/10^30,(-2663886959978571619156020987 : Int)/10^30)
theorem v2755_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 53 5) 1) 14) v2755_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2755 : Material (34 : Basis) (53 : Basis) where
  plus := ![v2755_pa,v2755_pb,v2755_pg]
  minus := ![(Primitive.Addresses.material2755 1).one,v2755_mb,v2755_mg]
  upper := v2755_upper
  lower := (Primitive.Addresses.material2755 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2755_pa_checked.trans (by decide +kernel)
    · exact v2755_pb_checked.trans (by decide +kernel)
    · exact v2755_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 53 Primitive.Addresses.material2755
    · exact v2755_mb_checked.trans (by decide +kernel)
    · exact v2755_mg_checked.trans (by decide +kernel)
  upper_error := v2755_upper_checked
  lower_error := reuse_lower_error 34 53 Primitive.Addresses.material2755

def v2756_pa : Scalar.QComplex := ((999999558329326579046457163076 : Int)/10^30,(-939862304685597721921830135 : Int)/10^30)
theorem v2756_pa_checked : Scalar.distance (sourceCoefficient 34 54 1 0) v2756_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2756_pb : Scalar.QComplex := ((-405529451314076335238216 : Int)/10^30,(-431477324052556757174684513 : Int)/10^30)
theorem v2756_pb_checked : Scalar.distance (sourceCoefficient 34 54 1 1) v2756_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2756_pg : Scalar.QComplex := ((-93086388095532929410672 : Int)/10^30,(87488425891397546757 : Int)/10^30)
theorem v2756_pg_checked : Scalar.distance (sourceCoefficient 34 54 1 2) v2756_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2756_mb : Scalar.QComplex := ((-777874797956996664628335 : Int)/10^30,(-431476813440177408970217062 : Int)/10^30)
theorem v2756_mb_checked : Scalar.distance (sourceCoefficient 34 54 3 1) v2756_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2756_mg : Scalar.QComplex := ((-93086277936645171497232 : Int)/10^30,(167817753786614519901 : Int)/10^30)
theorem v2756_mg_checked : Scalar.distance (sourceCoefficient 34 54 3 2) v2756_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2756_upper : Scalar.QComplex := ((999996446830378402223245300568 : Int)/10^30,(-2665769423296244814235580455 : Int)/10^30)
theorem v2756_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 54 5) 1) 14) v2756_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2756 : Material (34 : Basis) (54 : Basis) where
  plus := ![v2756_pa,v2756_pb,v2756_pg]
  minus := ![(Primitive.Addresses.material2756 1).one,v2756_mb,v2756_mg]
  upper := v2756_upper
  lower := (Primitive.Addresses.material2756 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2756_pa_checked.trans (by decide +kernel)
    · exact v2756_pb_checked.trans (by decide +kernel)
    · exact v2756_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 54 Primitive.Addresses.material2756
    · exact v2756_mb_checked.trans (by decide +kernel)
    · exact v2756_mg_checked.trans (by decide +kernel)
  upper_error := v2756_upper_checked
  lower_error := reuse_lower_error 34 54 Primitive.Addresses.material2756

def v2757_pa : Scalar.QComplex := ((999999543790746134906741181390 : Int)/10^30,(-955205893827766959665791212 : Int)/10^30)
theorem v2757_pa_checked : Scalar.distance (sourceCoefficient 34 55 1 0) v2757_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2757_pb : Scalar.QComplex := ((-412149864378645916108160 : Int)/10^30,(-431477317105393046796921621 : Int)/10^30)
theorem v2757_pb_checked : Scalar.distance (sourceCoefficient 34 55 1 1) v2757_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2757_pg : Scalar.QComplex := ((-93086386669474376390042 : Int)/10^30,(88916705746436387544 : Int)/10^30)
theorem v2757_pg_checked : Scalar.distance (sourceCoefficient 34 55 1 2) v2757_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2757_mb : Scalar.QComplex := ((-784495202561394500317353 : Int)/10^30,(-431476800779897982951207143 : Int)/10^30)
theorem v2757_mb_checked : Scalar.distance (sourceCoefficient 34 55 3 1) v2757_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2757_mg : Scalar.QComplex := ((-93086275278045961901584 : Int)/10^30,(169246031879215191079 : Int)/10^30)
theorem v2757_mg_checked : Scalar.distance (sourceCoefficient 34 55 3 2) v2757_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2757_upper : Scalar.QComplex := ((999996405810176711740761323102 : Int)/10^30,(-2681112964493669492439542160 : Int)/10^30)
theorem v2757_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 55 5) 1) 14) v2757_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2757 : Material (34 : Basis) (55 : Basis) where
  plus := ![v2757_pa,v2757_pb,v2757_pg]
  minus := ![(Primitive.Addresses.material2757 1).one,v2757_mb,v2757_mg]
  upper := v2757_upper
  lower := (Primitive.Addresses.material2757 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2757_pa_checked.trans (by decide +kernel)
    · exact v2757_pb_checked.trans (by decide +kernel)
    · exact v2757_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 55 Primitive.Addresses.material2757
    · exact v2757_mb_checked.trans (by decide +kernel)
    · exact v2757_mg_checked.trans (by decide +kernel)
  upper_error := v2757_upper_checked
  lower_error := reuse_lower_error 34 55 Primitive.Addresses.material2757

def v2758_pa : Scalar.QComplex := ((999999540305768205257131165615 : Int)/10^30,(-958847356084741463427888298 : Int)/10^30)
theorem v2758_pa_checked : Scalar.distance (sourceCoefficient 34 56 1 0) v2758_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2758_pb : Scalar.QComplex := ((-413721073302261397718654 : Int)/10^30,(-431477315436750716339307113 : Int)/10^30)
theorem v2758_pb_checked : Scalar.distance (sourceCoefficient 34 56 1 1) v2758_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2758_pg : Scalar.QComplex := ((-93086386327276877203203 : Int)/10^30,(89255676447711878940 : Int)/10^30)
theorem v2758_pg_checked : Scalar.distance (sourceCoefficient 34 56 1 2) v2758_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2758_mb : Scalar.QComplex := ((-786066409460013913546454 : Int)/10^30,(-431476797755373737348245712 : Int)/10^30)
theorem v2758_mb_checked : Scalar.distance (sourceCoefficient 34 56 3 1) v2758_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2758_mg : Scalar.QComplex := ((-93086274643332141603424 : Int)/10^30,(169585002158975368869 : Int)/10^30)
theorem v2758_mg_checked : Scalar.distance (sourceCoefficient 34 56 3 2) v2758_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2758_upper : Scalar.QComplex := ((999996396040370467893803067810 : Int)/10^30,(-2684754415312357968795940360 : Int)/10^30)
theorem v2758_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 56 5) 1) 14) v2758_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2758 : Material (34 : Basis) (56 : Basis) where
  plus := ![v2758_pa,v2758_pb,v2758_pg]
  minus := ![(Primitive.Addresses.material2758 1).one,v2758_mb,v2758_mg]
  upper := v2758_upper
  lower := (Primitive.Addresses.material2758 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2758_pa_checked.trans (by decide +kernel)
    · exact v2758_pb_checked.trans (by decide +kernel)
    · exact v2758_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 56 Primitive.Addresses.material2758
    · exact v2758_mb_checked.trans (by decide +kernel)
    · exact v2758_mg_checked.trans (by decide +kernel)
  upper_error := v2758_upper_checked
  lower_error := reuse_lower_error 34 56 Primitive.Addresses.material2758

def v2759_pa : Scalar.QComplex := ((999999528943242861716901111917 : Int)/10^30,(-970625206957916250128341570 : Int)/10^30)
theorem v2759_pa_checked : Scalar.distance (sourceCoefficient 34 57 1 0) v2759_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2759_pb : Scalar.QComplex := ((-418802950584219917248146 : Int)/10^30,(-431477309987497901741281337 : Int)/10^30)
theorem v2759_pb_checked : Scalar.distance (sourceCoefficient 34 57 1 1) v2759_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2759_pg : Scalar.QComplex := ((-93086385210620866829717 : Int)/10^30,(90352034470959552050 : Int)/10^30)
theorem v2759_pg_checked : Scalar.distance (sourceCoefficient 34 57 1 2) v2759_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2759_mb : Scalar.QComplex := ((-791148280147297513975520 : Int)/10^30,(-431476787920691736682265653 : Int)/10^30)
theorem v2759_mb_checked : Scalar.distance (sourceCoefficient 34 57 3 1) v2759_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2759_mg : Scalar.QComplex := ((-93086272580568951081628 : Int)/10^30,(170681358810374999255 : Int)/10^30)
theorem v2759_mg_checked : Scalar.distance (sourceCoefficient 34 57 3 2) v2759_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2759_upper : Scalar.QComplex := ((999996364350359918685374483957 : Int)/10^30,(-2696532229033119460749899918 : Int)/10^30)
theorem v2759_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 57 5) 1) 14) v2759_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2759 : Material (34 : Basis) (57 : Basis) where
  plus := ![v2759_pa,v2759_pb,v2759_pg]
  minus := ![(Primitive.Addresses.material2759 1).one,v2759_mb,v2759_mg]
  upper := v2759_upper
  lower := (Primitive.Addresses.material2759 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2759_pa_checked.trans (by decide +kernel)
    · exact v2759_pb_checked.trans (by decide +kernel)
    · exact v2759_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 57 Primitive.Addresses.material2759
    · exact v2759_mb_checked.trans (by decide +kernel)
    · exact v2759_mg_checked.trans (by decide +kernel)
  upper_error := v2759_upper_checked
  lower_error := reuse_lower_error 34 57 Primitive.Addresses.material2759

def v2760_pa : Scalar.QComplex := ((999999522719994106897019317920 : Int)/10^30,(-977015754217915329539433749 : Int)/10^30)
theorem v2760_pa_checked : Scalar.distance (sourceCoefficient 34 58 1 0) v2760_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2760_pb : Scalar.QComplex := ((-421560327726283962043885 : Int)/10^30,(-431477306997388233518216612 : Int)/10^30)
theorem v2760_pb_checked : Scalar.distance (sourceCoefficient 34 58 1 1) v2760_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2760_pg : Scalar.QComplex := ((-93086384598429570738372 : Int)/10^30,(90946907662994229800 : Int)/10^30)
theorem v2760_pg_checked : Scalar.distance (sourceCoefficient 34 58 1 2) v2760_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2760_mb : Scalar.QComplex := ((-793905653682334056283773 : Int)/10^30,(-431476782551090895868830571 : Int)/10^30)
theorem v2760_mb_checked : Scalar.distance (sourceCoefficient 34 58 3 1) v2760_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2760_mg : Scalar.QComplex := ((-93086271455029110305154 : Int)/10^30,(171276231252617684108 : Int)/10^30)
theorem v2760_mg_checked : Scalar.distance (sourceCoefficient 34 58 3 2) v2760_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2760_upper : Scalar.QComplex := ((999996347097615607823768308365 : Int)/10^30,(-2702922756034386300704119751 : Int)/10^30)
theorem v2760_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 58 5) 1) 14) v2760_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2760 : Material (34 : Basis) (58 : Basis) where
  plus := ![v2760_pa,v2760_pb,v2760_pg]
  minus := ![(Primitive.Addresses.material2760 1).one,v2760_mb,v2760_mg]
  upper := v2760_upper
  lower := (Primitive.Addresses.material2760 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2760_pa_checked.trans (by decide +kernel)
    · exact v2760_pb_checked.trans (by decide +kernel)
    · exact v2760_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 58 Primitive.Addresses.material2760
    · exact v2760_mb_checked.trans (by decide +kernel)
    · exact v2760_mg_checked.trans (by decide +kernel)
  upper_error := v2760_upper_checked
  lower_error := reuse_lower_error 34 58 Primitive.Addresses.material2760

def v2761_pa : Scalar.QComplex := ((999999505403525846816676623827 : Int)/10^30,(-994581672705009380815720331 : Int)/10^30)
theorem v2761_pa_checked : Scalar.distance (sourceCoefficient 34 59 1 0) v2761_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2761_pb : Scalar.QComplex := ((-429139625683783329709294 : Int)/10^30,(-431477298657321330500797614 : Int)/10^30)
theorem v2761_pb_checked : Scalar.distance (sourceCoefficient 34 59 1 1) v2761_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2761_pg : Scalar.QComplex := ((-93086382892827576918180 : Int)/10^30,(92582056194365985010 : Int)/10^30)
theorem v2761_pg_checked : Scalar.distance (sourceCoefficient 34 59 1 2) v2761_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2761_mb : Scalar.QComplex := ((-801484941620612288708956 : Int)/10^30,(-431476767670434319825692614 : Int)/10^30)
theorem v2761_mb_checked : Scalar.distance (sourceCoefficient 34 59 3 1) v2761_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2761_mg : Scalar.QComplex := ((-93086268338368213340755 : Int)/10^30,(172911377703291207904 : Int)/10^30)
theorem v2761_mg_checked : Scalar.distance (sourceCoefficient 34 59 3 2) v2761_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2761_upper : Scalar.QComplex := ((999996299463991397541312870464 : Int)/10^30,(-2720488618472454924018297032 : Int)/10^30)
theorem v2761_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 59 5) 1) 14) v2761_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2761 : Material (34 : Basis) (59 : Basis) where
  plus := ![v2761_pa,v2761_pb,v2761_pg]
  minus := ![(Primitive.Addresses.material2761 1).one,v2761_mb,v2761_mg]
  upper := v2761_upper
  lower := (Primitive.Addresses.material2761 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2761_pa_checked.trans (by decide +kernel)
    · exact v2761_pb_checked.trans (by decide +kernel)
    · exact v2761_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 59 Primitive.Addresses.material2761
    · exact v2761_mb_checked.trans (by decide +kernel)
    · exact v2761_mg_checked.trans (by decide +kernel)
  upper_error := v2761_upper_checked
  lower_error := reuse_lower_error 34 59 Primitive.Addresses.material2761

def v2762_pa : Scalar.QComplex := ((999999485044078922216475654608 : Int)/10^30,(-1014845592677017243803537000 : Int)/10^30)
theorem v2762_pa_checked : Scalar.distance (sourceCoefficient 34 60 1 0) v2762_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2762_pb : Scalar.QComplex := ((-437883050385382512162131 : Int)/10^30,(-431477288815770322398081631 : Int)/10^30)
theorem v2762_pb_checked : Scalar.distance (sourceCoefficient 34 60 1 1) v2762_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2762_pg : Scalar.QComplex := ((-93086380883631405680501 : Int)/10^30,(94468352025044711786 : Int)/10^30)
theorem v2762_pg_checked : Scalar.distance (sourceCoefficient 34 60 1 2) v2762_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2762_mb : Scalar.QComplex := ((-810228354573819587517857 : Int)/10^30,(-431476750283705247932520254 : Int)/10^30)
theorem v2762_mb_checked : Scalar.distance (sourceCoefficient 34 60 3 1) v2762_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2762_mg : Scalar.QComplex := ((-93086264701384443953408 : Int)/10^30,(174797671097769983999 : Int)/10^30)
theorem v2762_mg_checked : Scalar.distance (sourceCoefficient 34 60 3 2) v2762_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2762_upper : Scalar.QComplex := ((999996244130887252719772633828 : Int)/10^30,(-2740752473125175958689116121 : Int)/10^30)
theorem v2762_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 60 5) 1) 14) v2762_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2762 : Material (34 : Basis) (60 : Basis) where
  plus := ![v2762_pa,v2762_pb,v2762_pg]
  minus := ![(Primitive.Addresses.material2762 1).one,v2762_mb,v2762_mg]
  upper := v2762_upper
  lower := (Primitive.Addresses.material2762 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2762_pa_checked.trans (by decide +kernel)
    · exact v2762_pb_checked.trans (by decide +kernel)
    · exact v2762_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 60 Primitive.Addresses.material2762
    · exact v2762_mb_checked.trans (by decide +kernel)
    · exact v2762_mg_checked.trans (by decide +kernel)
  upper_error := v2762_upper_checked
  lower_error := reuse_lower_error 34 60 Primitive.Addresses.material2762

def v2763_pa : Scalar.QComplex := ((999999479080592128639703232951 : Int)/10^30,(-1020704925228486930947875472 : Int)/10^30)
theorem v2763_pa_checked : Scalar.distance (sourceCoefficient 34 61 1 0) v2763_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2763_pb : Scalar.QComplex := ((-440411220287688050900481 : Int)/10^30,(-431477285926046685725396408 : Int)/10^30)
theorem v2763_pb_checked : Scalar.distance (sourceCoefficient 34 61 1 1) v2763_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2763_pg : Scalar.QComplex := ((-93086380294358845871561 : Int)/10^30,(95013776332664151878 : Int)/10^30)
theorem v2763_pg_checked : Scalar.distance (sourceCoefficient 34 61 1 2) v2763_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2763_mb : Scalar.QComplex := ((-812756521041070578428111 : Int)/10^30,(-431476745212285926091881153 : Int)/10^30)
theorem v2763_mb_checked : Scalar.distance (sourceCoefficient 34 61 3 1) v2763_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2763_mg : Scalar.QComplex := ((-93086263641435491080915 : Int)/10^30,(175343094693787347977 : Int)/10^30)
theorem v2763_mg_checked : Scalar.distance (sourceCoefficient 34 61 3 2) v2763_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2763_upper : Scalar.QComplex := ((999996228054732911716172337287 : Int)/10^30,(-2746611786657420893552592383 : Int)/10^30)
theorem v2763_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 61 5) 1) 14) v2763_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2763 : Material (34 : Basis) (61 : Basis) where
  plus := ![v2763_pa,v2763_pb,v2763_pg]
  minus := ![(Primitive.Addresses.material2763 1).one,v2763_mb,v2763_mg]
  upper := v2763_upper
  lower := (Primitive.Addresses.material2763 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2763_pa_checked.trans (by decide +kernel)
    · exact v2763_pb_checked.trans (by decide +kernel)
    · exact v2763_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 61 Primitive.Addresses.material2763
    · exact v2763_mb_checked.trans (by decide +kernel)
    · exact v2763_mg_checked.trans (by decide +kernel)
  upper_error := v2763_upper_checked
  lower_error := reuse_lower_error 34 61 Primitive.Addresses.material2763

def v2764_pa : Scalar.QComplex := ((999999470354721678467095916297 : Int)/10^30,(-1029218283999533774252961919 : Int)/10^30)
theorem v2764_pa_checked : Scalar.distance (sourceCoefficient 34 62 1 0) v2764_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2764_pb : Scalar.QComplex := ((-444084542655316053257138 : Int)/10^30,(-431477281692205174728127274 : Int)/10^30)
theorem v2764_pb_checked : Scalar.distance (sourceCoefficient 34 62 1 1) v2764_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2764_pg : Scalar.QComplex := ((-93086379431526900995044 : Int)/10^30,(95806254445575914046 : Int)/10^30)
theorem v2764_pg_checked : Scalar.distance (sourceCoefficient 34 62 1 2) v2764_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2764_mb : Scalar.QComplex := ((-816429838387338245343712 : Int)/10^30,(-431476737808534228582342068 : Int)/10^30)
theorem v2764_mb_checked : Scalar.distance (sourceCoefficient 34 62 3 1) v2764_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2764_mg : Scalar.QComplex := ((-93086262094730947922575 : Int)/10^30,(176135571767038182749 : Int)/10^30)
theorem v2764_mg_checked : Scalar.distance (sourceCoefficient 34 62 3 2) v2764_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2764_upper : Scalar.QComplex := ((999996204635590544750366984515 : Int)/10^30,(-2755125117688759104539931886 : Int)/10^30)
theorem v2764_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 62 5) 1) 14) v2764_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2764 : Material (34 : Basis) (62 : Basis) where
  plus := ![v2764_pa,v2764_pb,v2764_pg]
  minus := ![(Primitive.Addresses.material2764 1).one,v2764_mb,v2764_mg]
  upper := v2764_upper
  lower := (Primitive.Addresses.material2764 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2764_pa_checked.trans (by decide +kernel)
    · exact v2764_pb_checked.trans (by decide +kernel)
    · exact v2764_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 62 Primitive.Addresses.material2764
    · exact v2764_mb_checked.trans (by decide +kernel)
    · exact v2764_mg_checked.trans (by decide +kernel)
  upper_error := v2764_upper_checked
  lower_error := reuse_lower_error 34 62 Primitive.Addresses.material2764

def v2765_pa : Scalar.QComplex := ((999999444527675263504092132618 : Int)/10^30,(-1054013444375112450381084071 : Int)/10^30)
theorem v2765_pa_checked : Scalar.distance (sourceCoefficient 34 63 1 0) v2765_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2765_pb : Scalar.QComplex := ((-454783095217925946786955 : Int)/10^30,(-431477269123571349362952628 : Int)/10^30)
theorem v2765_pb_checked : Scalar.distance (sourceCoefficient 34 63 1 1) v2765_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2765_pg : Scalar.QComplex := ((-93086376873682324395611 : Int)/10^30,(98114347212834254941 : Int)/10^30)
theorem v2765_pg_checked : Scalar.distance (sourceCoefficient 34 63 1 2) v2765_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2765_mb : Scalar.QComplex := ((-827128376120223150771066 : Int)/10^30,(-431476716007536066482113150 : Int)/10^30)
theorem v2765_mb_checked : Scalar.distance (sourceCoefficient 34 63 3 1) v2765_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2765_mg : Scalar.QComplex := ((-93086257545107218220962 : Int)/10^30,(178443661467583432781 : Int)/10^30)
theorem v2765_mg_checked : Scalar.distance (sourceCoefficient 34 63 3 2) v2765_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2765_upper : Scalar.QComplex := ((999996136014385187268274146480 : Int)/10^30,(-2779920196559719944505443615 : Int)/10^30)
theorem v2765_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 63 5) 1) 14) v2765_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2765 : Material (34 : Basis) (63 : Basis) where
  plus := ![v2765_pa,v2765_pb,v2765_pg]
  minus := ![(Primitive.Addresses.material2765 1).one,v2765_mb,v2765_mg]
  upper := v2765_upper
  lower := (Primitive.Addresses.material2765 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2765_pa_checked.trans (by decide +kernel)
    · exact v2765_pb_checked.trans (by decide +kernel)
    · exact v2765_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 63 Primitive.Addresses.material2765
    · exact v2765_mb_checked.trans (by decide +kernel)
    · exact v2765_mg_checked.trans (by decide +kernel)
  upper_error := v2765_upper_checked
  lower_error := reuse_lower_error 34 63 Primitive.Addresses.material2765

def v2766_pa : Scalar.QComplex := ((999999406548414969341272456658 : Int)/10^30,(-1089450695477557478843710631 : Int)/10^30)
theorem v2766_pa_checked : Scalar.distance (sourceCoefficient 34 64 1 0) v2766_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2766_pb : Scalar.QComplex := ((-470073469656464495514474 : Int)/10^30,(-431477250546490916759625674 : Int)/10^30)
theorem v2766_pb_checked : Scalar.distance (sourceCoefficient 34 64 1 1) v2766_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2766_pg : Scalar.QComplex := ((-93086373102107203292417 : Int)/10^30,(101413074099323659320 : Int)/10^30)
theorem v2766_pg_checked : Scalar.distance (sourceCoefficient 34 64 1 2) v2766_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2766_mb : Scalar.QComplex := ((-842418728834272758704161 : Int)/10^30,(-431476684235558063416792676 : Int)/10^30)
theorem v2766_mb_checked : Scalar.distance (sourceCoefficient 34 64 3 1) v2766_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2766_mg : Scalar.QComplex := ((-93086250926880767551021 : Int)/10^30,(181742383871106593979 : Int)/10^30)
theorem v2766_mg_checked : Scalar.distance (sourceCoefficient 34 64 3 2) v2766_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2766_upper : Scalar.QComplex := ((999996036873700898239230061881 : Int)/10^30,(-2815357329333784391662536778 : Int)/10^30)
theorem v2766_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 64 5) 1) 14) v2766_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2766 : Material (34 : Basis) (64 : Basis) where
  plus := ![v2766_pa,v2766_pb,v2766_pg]
  minus := ![(Primitive.Addresses.material2766 1).one,v2766_mb,v2766_mg]
  upper := v2766_upper
  lower := (Primitive.Addresses.material2766 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2766_pa_checked.trans (by decide +kernel)
    · exact v2766_pb_checked.trans (by decide +kernel)
    · exact v2766_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 64 Primitive.Addresses.material2766
    · exact v2766_mb_checked.trans (by decide +kernel)
    · exact v2766_mg_checked.trans (by decide +kernel)
  upper_error := v2766_upper_checked
  lower_error := reuse_lower_error 34 64 Primitive.Addresses.material2766

def v2767_pa : Scalar.QComplex := ((999999366717758577645738663945 : Int)/10^30,(-1125417292295756055285336598 : Int)/10^30)
theorem v2767_pa_checked : Scalar.distance (sourceCoefficient 34 65 1 0) v2767_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2767_pb : Scalar.QComplex := ((-485592244463543172868239 : Int)/10^30,(-431477230953179789876259959 : Int)/10^30)
theorem v2767_pb_checked : Scalar.distance (sourceCoefficient 34 65 1 1) v2767_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2767_pg : Scalar.QComplex := ((-93086369134741975178786 : Int)/10^30,(104761075844593478842 : Int)/10^30)
theorem v2767_pg_checked : Scalar.distance (sourceCoefficient 34 65 1 2) v2767_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2767_mb : Scalar.QComplex := ((-857937480954857279811261 : Int)/10^30,(-431476651250250513181170122 : Int)/10^30)
theorem v2767_mb_checked : Scalar.distance (sourceCoefficient 34 65 3 1) v2767_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2767_mg : Scalar.QComplex := ((-93086244070342298902006 : Int)/10^30,(185090380946104844133 : Int)/10^30)
theorem v2767_mg_checked : Scalar.distance (sourceCoefficient 34 65 3 2) v2767_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2767_upper : Scalar.QComplex := ((999995934968020585592061974746 : Int)/10^30,(-2851323803839862417499984089 : Int)/10^30)
theorem v2767_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 65 5) 1) 14) v2767_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2767 : Material (34 : Basis) (65 : Basis) where
  plus := ![v2767_pa,v2767_pb,v2767_pg]
  minus := ![(Primitive.Addresses.material2767 1).one,v2767_mb,v2767_mg]
  upper := v2767_upper
  lower := (Primitive.Addresses.material2767 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2767_pa_checked.trans (by decide +kernel)
    · exact v2767_pb_checked.trans (by decide +kernel)
    · exact v2767_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 65 Primitive.Addresses.material2767
    · exact v2767_mb_checked.trans (by decide +kernel)
    · exact v2767_mg_checked.trans (by decide +kernel)
  upper_error := v2767_upper_checked
  lower_error := reuse_lower_error 34 65 Primitive.Addresses.material2767

def v2768_pa : Scalar.QComplex := ((999999346769745937661187033060 : Int)/10^30,(-1143004847502806001807511538 : Int)/10^30)
theorem v2768_pa_checked : Scalar.distance (sourceCoefficient 34 66 1 0) v2768_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2768_pb : Scalar.QComplex := ((-493180877466353242907142 : Int)/10^30,(-431477221101175278271701710 : Int)/10^30)
theorem v2768_pb_checked : Scalar.distance (sourceCoefficient 34 66 1 1) v2768_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2768_pg : Scalar.QComplex := ((-93086367143567664894915 : Int)/10^30,(106398238384072061346 : Int)/10^30)
theorem v2768_pg_checked : Scalar.distance (sourceCoefficient 34 66 1 2) v2768_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2768_mb : Scalar.QComplex := ((-865526102630236289539496 : Int)/10^30,(-431476634849601167846060924 : Int)/10^30)
theorem v2768_mb_checked : Scalar.distance (sourceCoefficient 34 66 3 1) v2768_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2768_mg : Scalar.QComplex := ((-93086240666371193516919 : Int)/10^30,(186727541157699240552 : Int)/10^30)
theorem v2768_mg_checked : Scalar.distance (sourceCoefficient 34 66 3 2) v2768_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2768_upper : Scalar.QComplex := ((999995884665512899005654671632 : Int)/10^30,(-2868911298423854715440018866 : Int)/10^30)
theorem v2768_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 66 5) 1) 14) v2768_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2768 : Material (34 : Basis) (66 : Basis) where
  plus := ![v2768_pa,v2768_pb,v2768_pg]
  minus := ![(Primitive.Addresses.material2768 1).one,v2768_mb,v2768_mg]
  upper := v2768_upper
  lower := (Primitive.Addresses.material2768 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2768_pa_checked.trans (by decide +kernel)
    · exact v2768_pb_checked.trans (by decide +kernel)
    · exact v2768_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 66 Primitive.Addresses.material2768
    · exact v2768_mb_checked.trans (by decide +kernel)
    · exact v2768_mg_checked.trans (by decide +kernel)
  upper_error := v2768_upper_checked
  lower_error := reuse_lower_error 34 66 Primitive.Addresses.material2768

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
