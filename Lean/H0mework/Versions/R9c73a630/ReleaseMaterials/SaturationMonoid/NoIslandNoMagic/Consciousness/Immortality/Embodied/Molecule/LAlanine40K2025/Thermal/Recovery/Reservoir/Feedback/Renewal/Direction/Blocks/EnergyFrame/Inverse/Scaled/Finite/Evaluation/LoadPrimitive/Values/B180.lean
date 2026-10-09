import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B120

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2881_pa : Scalar.QComplex := ((999999473298234137390522527367 : Int)/10^30,(-1026354351240578505179588967 : Int)/10^30)
theorem v2881_pa_checked : Scalar.distance (sourceCoefficient 36 56 1 0) v2881_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2881_pb : Scalar.QComplex := ((-442848826555504752929701 : Int)/10^30,(-431477289272427544557445334 : Int)/10^30)
theorem v2881_pb_checked : Scalar.distance (sourceCoefficient 36 56 1 1) v2881_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2881_pg : Scalar.QComplex := ((-93086380386201357392435 : Int)/10^30,(95539661871522023415 : Int)/10^30)
theorem v2881_pg_checked : Scalar.distance (sourceCoefficient 36 56 1 2) v2881_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2881_mb : Scalar.QComplex := ((-815194129289031028612254 : Int)/10^30,(-431476746455121115498450633 : Int)/10^30)
theorem v2881_mb_checked : Scalar.distance (sourceCoefficient 36 56 3 1) v2881_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2881_mg : Scalar.QComplex := ((-93086263279462433375723 : Int)/10^30,(175868980116089950250 : Int)/10^30)
theorem v2881_mg_checked : Scalar.distance (sourceCoefficient 36 56 3 2) v2881_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2881_upper : Scalar.QComplex := ((999996212521986747664212491474 : Int)/10^30,(-2752261194275530729493777754 : Int)/10^30)
theorem v2881_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 56 5) 1) 14) v2881_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2881 : Material (36 : Basis) (56 : Basis) where
  plus := ![v2881_pa,v2881_pb,v2881_pg]
  minus := ![(Primitive.Addresses.material2881 1).one,v2881_mb,v2881_mg]
  upper := v2881_upper
  lower := (Primitive.Addresses.material2881 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2881_pa_checked.trans (by decide +kernel)
    · exact v2881_pb_checked.trans (by decide +kernel)
    · exact v2881_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 56 Primitive.Addresses.material2881
    · exact v2881_mb_checked.trans (by decide +kernel)
    · exact v2881_mg_checked.trans (by decide +kernel)
  upper_error := v2881_upper_checked
  lower_error := reuse_lower_error 36 56 Primitive.Addresses.material2881

def v2882_pa : Scalar.QComplex := ((999999461140621106669528772607 : Int)/10^30,(-1038132201319865966688467484 : Int)/10^30)
theorem v2882_pa_checked : Scalar.distance (sourceCoefficient 36 57 1 0) v2882_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2882_pb : Scalar.QComplex := ((-447930703609100252434885 : Int)/10^30,(-431477283594466423801416679 : Int)/10^30)
theorem v2882_pb_checked : Scalar.distance (sourceCoefficient 36 57 1 1) v2882_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2882_pg : Scalar.QComplex := ((-93086379207868785488640 : Int)/10^30,(96636019833186249504 : Int)/10^30)
theorem v2882_pg_checked : Scalar.distance (sourceCoefficient 36 57 1 2) v2882_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2882_mb : Scalar.QComplex := ((-820275999550586726472377 : Int)/10^30,(-431476736391731090900023755 : Int)/10^30)
theorem v2882_mb_checked : Scalar.distance (sourceCoefficient 36 57 3 1) v2882_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2882_mg : Scalar.QComplex := ((-93086261155022757432361 : Int)/10^30,(176965336652682061753 : Int)/10^30)
theorem v2882_mg_checked : Scalar.distance (sourceCoefficient 36 57 3 2) v2882_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2882_upper : Scalar.QComplex := ((999996180036891065642235086863 : Int)/10^30,(-2764039005830156860375612754 : Int)/10^30)
theorem v2882_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 57 5) 1) 14) v2882_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2882 : Material (36 : Basis) (57 : Basis) where
  plus := ![v2882_pa,v2882_pb,v2882_pg]
  minus := ![(Primitive.Addresses.material2882 1).one,v2882_mb,v2882_mg]
  upper := v2882_upper
  lower := (Primitive.Addresses.material2882 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2882_pa_checked.trans (by decide +kernel)
    · exact v2882_pb_checked.trans (by decide +kernel)
    · exact v2882_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 57 Primitive.Addresses.material2882
    · exact v2882_mb_checked.trans (by decide +kernel)
    · exact v2882_mg_checked.trans (by decide +kernel)
  upper_error := v2882_upper_checked
  lower_error := reuse_lower_error 36 57 Primitive.Addresses.material2882

def v2883_pa : Scalar.QComplex := ((999999454485965510828536389560 : Int)/10^30,(-1044522748145190518410254266 : Int)/10^30)
theorem v2883_pa_checked : Scalar.distance (sourceCoefficient 36 58 1 0) v2883_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2883_pb : Scalar.QComplex := ((-450688080626129440685876 : Int)/10^30,(-431477280480261854584171210 : Int)/10^30)
theorem v2883_pb_checked : Scalar.distance (sourceCoefficient 36 58 1 1) v2883_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2883_pg : Scalar.QComplex := ((-93086378562212387377312 : Int)/10^30,(97230892991502344163 : Int)/10^30)
theorem v2883_pg_checked : Scalar.distance (sourceCoefficient 36 58 1 2) v2883_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2883_mb : Scalar.QComplex := ((-823033372853500148260961 : Int)/10^30,(-431476730898035503198060824 : Int)/10^30)
theorem v2883_mb_checked : Scalar.distance (sourceCoefficient 36 58 3 1) v2883_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2883_mg : Scalar.QComplex := ((-93086259996017856194109 : Int)/10^30,(177560209032327300239 : Int)/10^30)
theorem v2883_mg_checked : Scalar.distance (sourceCoefficient 36 58 3 2) v2883_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2883_upper : Scalar.QComplex := ((999996162352741306498132842407 : Int)/10^30,(-2770429531652180749357635421 : Int)/10^30)
theorem v2883_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 58 5) 1) 14) v2883_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2883 : Material (36 : Basis) (58 : Basis) where
  plus := ![v2883_pa,v2883_pb,v2883_pg]
  minus := ![(Primitive.Addresses.material2883 1).one,v2883_mb,v2883_mg]
  upper := v2883_upper
  lower := (Primitive.Addresses.material2883 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2883_pa_checked.trans (by decide +kernel)
    · exact v2883_pb_checked.trans (by decide +kernel)
    · exact v2883_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 58 Primitive.Addresses.material2883
    · exact v2883_mb_checked.trans (by decide +kernel)
    · exact v2883_mg_checked.trans (by decide +kernel)
  upper_error := v2883_upper_checked
  lower_error := reuse_lower_error 36 58 Primitive.Addresses.material2883

def v2884_pa : Scalar.QComplex := ((999999435983674332494899554488 : Int)/10^30,(-1062088665423275563457165993 : Int)/10^30)
theorem v2884_pa_checked : Scalar.distance (sourceCoefficient 36 59 1 0) v2884_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2884_pb : Scalar.QComplex := ((-458267378235855341274062 : Int)/10^30,(-431477271799091001565689398 : Int)/10^30)
theorem v2884_pb_checked : Scalar.distance (sourceCoefficient 36 59 1 1) v2884_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2884_pg : Scalar.QComplex := ((-93086376764623709188232 : Int)/10^30,(98866041429088823220 : Int)/10^30)
theorem v2884_pg_checked : Scalar.distance (sourceCoefficient 36 59 1 2) v2884_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2884_mb : Scalar.QComplex := ((-830612660149647697001576 : Int)/10^30,(-431476715676275404275288811 : Int)/10^30)
theorem v2884_mb_checked : Scalar.distance (sourceCoefficient 36 59 3 1) v2884_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2884_mg : Scalar.QComplex := ((-93086256787370390044139 : Int)/10^30,(179195355309835217120 : Int)/10^30)
theorem v2884_mg_checked : Scalar.distance (sourceCoefficient 36 59 3 2) v2884_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2884_upper : Scalar.QComplex := ((999996113533298030746187768414 : Int)/10^30,(-2787995390834619387228945179 : Int)/10^30)
theorem v2884_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 59 5) 1) 14) v2884_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2884 : Material (36 : Basis) (59 : Basis) where
  plus := ![v2884_pa,v2884_pb,v2884_pg]
  minus := ![(Primitive.Addresses.material2884 1).one,v2884_mb,v2884_mg]
  upper := v2884_upper
  lower := (Primitive.Addresses.material2884 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2884_pa_checked.trans (by decide +kernel)
    · exact v2884_pb_checked.trans (by decide +kernel)
    · exact v2884_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 59 Primitive.Addresses.material2884
    · exact v2884_mb_checked.trans (by decide +kernel)
    · exact v2884_mg_checked.trans (by decide +kernel)
  upper_error := v2884_upper_checked
  lower_error := reuse_lower_error 36 59 Primitive.Addresses.material2884

def v2885_pa : Scalar.QComplex := ((999999414256270433781965996820 : Int)/10^30,(-1082352583974704308491286517 : Int)/10^30)
theorem v2885_pa_checked : Scalar.distance (sourceCoefficient 36 60 1 0) v2885_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2885_pb : Scalar.QComplex := ((-467010802528822559890817 : Int)/10^30,(-431477261564044877493701490 : Int)/10^30)
theorem v2885_pb_checked : Scalar.distance (sourceCoefficient 36 60 1 1) v2885_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2885_pg : Scalar.QComplex := ((-93086374649312346230376 : Int)/10^30,(100752337149570352051 : Int)/10^30)
theorem v2885_pg_checked : Scalar.distance (sourceCoefficient 36 60 1 2) v2885_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2885_mb : Scalar.QComplex := ((-839356072354654621407407 : Int)/10^30,(-431476697896051715560040507 : Int)/10^30)
theorem v2885_mb_checked : Scalar.distance (sourceCoefficient 36 60 3 1) v2885_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2885_mg : Scalar.QComplex := ((-93086253044271563543369 : Int)/10^30,(181081648502544205097 : Int)/10^30)
theorem v2885_mg_checked : Scalar.distance (sourceCoefficient 36 60 3 2) v2885_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2885_upper : Scalar.QComplex := ((999996056832241401013820027309 : Int)/10^30,(-2808259241705793782500489748 : Int)/10^30)
theorem v2885_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 60 5) 1) 14) v2885_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2885 : Material (36 : Basis) (60 : Basis) where
  plus := ![v2885_pa,v2885_pb,v2885_pg]
  minus := ![(Primitive.Addresses.material2885 1).one,v2885_mb,v2885_mg]
  upper := v2885_upper
  lower := (Primitive.Addresses.material2885 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2885_pa_checked.trans (by decide +kernel)
    · exact v2885_pb_checked.trans (by decide +kernel)
    · exact v2885_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 60 Primitive.Addresses.material2885
    · exact v2885_mb_checked.trans (by decide +kernel)
    · exact v2885_mg_checked.trans (by decide +kernel)
  upper_error := v2885_upper_checked
  lower_error := reuse_lower_error 36 60 Primitive.Addresses.material2885

def v2886_pa : Scalar.QComplex := ((999999407897237524993174997881 : Int)/10^30,(-1088211916110245651572948743 : Int)/10^30)
theorem v2886_pa_checked : Scalar.distance (sourceCoefficient 36 61 1 0) v2886_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2886_pb : Scalar.QComplex := ((-469538972311485613565540 : Int)/10^30,(-431477258560541738039790814 : Int)/10^30)
theorem v2886_pb_checked : Scalar.distance (sourceCoefficient 36 61 1 1) v2886_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2886_pg : Scalar.QComplex := ((-93086374029356473552527 : Int)/10^30,(101297761424925388522 : Int)/10^30)
theorem v2886_pg_checked : Scalar.distance (sourceCoefficient 36 61 1 2) v2886_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2886_mb : Scalar.QComplex := ((-841884238604076585340779 : Int)/10^30,(-431476692710853036549560931 : Int)/10^30)
theorem v2886_mb_checked : Scalar.distance (sourceCoefficient 36 61 3 1) v2886_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2886_mg : Scalar.QComplex := ((-93086251953639337069495 : Int)/10^30,(181627072039818860387 : Int)/10^30)
theorem v2886_mg_checked : Scalar.distance (sourceCoefficient 36 61 3 2) v2886_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2886_upper : Scalar.QComplex := ((999996040360542251772264778726 : Int)/10^30,(-2814118554139434281585020046 : Int)/10^30)
theorem v2886_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 61 5) 1) 14) v2886_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2886 : Material (36 : Basis) (61 : Basis) where
  plus := ![v2886_pa,v2886_pb,v2886_pg]
  minus := ![(Primitive.Addresses.material2886 1).one,v2886_mb,v2886_mg]
  upper := v2886_upper
  lower := (Primitive.Addresses.material2886 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2886_pa_checked.trans (by decide +kernel)
    · exact v2886_pb_checked.trans (by decide +kernel)
    · exact v2886_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 61 Primitive.Addresses.material2886
    · exact v2886_mb_checked.trans (by decide +kernel)
    · exact v2886_mg_checked.trans (by decide +kernel)
  upper_error := v2886_upper_checked
  lower_error := reuse_lower_error 36 61 Primitive.Addresses.material2886

def v2887_pa : Scalar.QComplex := ((999999398596655542594550167371 : Int)/10^30,(-1096725274272836376267438603 : Int)/10^30)
theorem v2887_pa_checked : Scalar.distance (sourceCoefficient 36 62 1 0) v2887_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2887_pb : Scalar.QComplex := ((-473212294504090194013725 : Int)/10^30,(-431477254161383491946371902 : Int)/10^30)
theorem v2887_pb_checked : Scalar.distance (sourceCoefficient 36 62 1 1) v2887_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2887_pg : Scalar.QComplex := ((-93086373121942991734482 : Int)/10^30,(102090239490637977872 : Int)/10^30)
theorem v2887_pg_checked : Scalar.distance (sourceCoefficient 36 62 1 2) v2887_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2887_mb : Scalar.QComplex := ((-845557555632659998718505 : Int)/10^30,(-431476685141784816536178238 : Int)/10^30)
theorem v2887_mb_checked : Scalar.distance (sourceCoefficient 36 62 3 1) v2887_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2887_mg : Scalar.QComplex := ((-93086250362353314300129 : Int)/10^30,(182419549027398681413 : Int)/10^30)
theorem v2887_mg_checked : Scalar.distance (sourceCoefficient 36 62 3 2) v2887_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2887_upper : Scalar.QComplex := ((999996016366690258685820817831 : Int)/10^30,(-2822631883570417312986499474 : Int)/10^30)
theorem v2887_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 62 5) 1) 14) v2887_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2887 : Material (36 : Basis) (62 : Basis) where
  plus := ![v2887_pa,v2887_pb,v2887_pg]
  minus := ![(Primitive.Addresses.material2887 1).one,v2887_mb,v2887_mg]
  upper := v2887_upper
  lower := (Primitive.Addresses.material2887 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2887_pa_checked.trans (by decide +kernel)
    · exact v2887_pb_checked.trans (by decide +kernel)
    · exact v2887_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 62 Primitive.Addresses.material2887
    · exact v2887_mb_checked.trans (by decide +kernel)
    · exact v2887_mg_checked.trans (by decide +kernel)
  upper_error := v2887_upper_checked
  lower_error := reuse_lower_error 36 62 Primitive.Addresses.material2887

def v2888_pa : Scalar.QComplex := ((999999371095761591487376656764 : Int)/10^30,(-1121520432848409658654969633 : Int)/10^30)
theorem v2888_pa_checked : Scalar.distance (sourceCoefficient 36 63 1 0) v2888_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2888_pb : Scalar.QComplex := ((-483910846548925520976066 : Int)/10^30,(-431477241111264619079937077 : Int)/10^30)
theorem v2888_pb_checked : Scalar.distance (sourceCoefficient 36 63 1 1) v2888_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2888_pg : Scalar.QComplex := ((-93086370434254673485126 : Int)/10^30,(104398332118266256728 : Int)/10^30)
theorem v2888_pg_checked : Scalar.distance (sourceCoefficient 36 63 1 2) v2888_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2888_mb : Scalar.QComplex := ((-856256092432270619657474 : Int)/10^30,(-431476662859302233029708526 : Int)/10^30)
theorem v2888_mb_checked : Scalar.distance (sourceCoefficient 36 63 3 1) v2888_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2888_mg : Scalar.QComplex := ((-93086245682886011789809 : Int)/10^30,(184727638476264620297 : Int)/10^30)
theorem v2888_mg_checked : Scalar.distance (sourceCoefficient 36 63 3 2) v2888_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2888_upper : Scalar.QComplex := ((999995946071642964704853778466 : Int)/10^30,(-2847426957752466442985463468 : Int)/10^30)
theorem v2888_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 63 5) 1) 14) v2888_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2888 : Material (36 : Basis) (63 : Basis) where
  plus := ![v2888_pa,v2888_pb,v2888_pg]
  minus := ![(Primitive.Addresses.material2888 1).one,v2888_mb,v2888_mg]
  upper := v2888_upper
  lower := (Primitive.Addresses.material2888 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2888_pa_checked.trans (by decide +kernel)
    · exact v2888_pb_checked.trans (by decide +kernel)
    · exact v2888_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 63 Primitive.Addresses.material2888
    · exact v2888_mb_checked.trans (by decide +kernel)
    · exact v2888_mg_checked.trans (by decide +kernel)
  upper_error := v2888_upper_checked
  lower_error := reuse_lower_error 36 63 Primitive.Addresses.material2888

def v2889_pa : Scalar.QComplex := ((999999330724237868221066138866 : Int)/10^30,(-1156957681306240384238803037 : Int)/10^30)
theorem v2889_pa_checked : Scalar.distance (sourceCoefficient 36 64 1 0) v2889_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2889_pb : Scalar.QComplex := ((-499201220226736337430749 : Int)/10^30,(-431477221846045605586281843 : Int)/10^30)
theorem v2889_pb_checked : Scalar.distance (sourceCoefficient 36 64 1 1) v2889_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2889_pg : Scalar.QComplex := ((-93086366477106835924085 : Int)/10^30,(107697058799607576576 : Int)/10^30)
theorem v2889_pg_checked : Scalar.distance (sourceCoefficient 36 64 1 2) v2889_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2889_mb : Scalar.QComplex := ((-871546443791760175874265 : Int)/10^30,(-431476630399186561773273971 : Int)/10^30)
theorem v2889_mb_checked : Scalar.distance (sourceCoefficient 36 64 3 1) v2889_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2889_mg : Scalar.QComplex := ((-93086238879087090792781 : Int)/10^30,(188026360514498876932 : Int)/10^30)
theorem v2889_mg_checked : Scalar.distance (sourceCoefficient 36 64 3 2) v2889_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2889_upper : Scalar.QComplex := ((999995844538703373932050732341 : Int)/10^30,(-2882864083753090871916470557 : Int)/10^30)
theorem v2889_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 64 5) 1) 14) v2889_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2889 : Material (36 : Basis) (64 : Basis) where
  plus := ![v2889_pa,v2889_pb,v2889_pg]
  minus := ![(Primitive.Addresses.material2889 1).one,v2889_mb,v2889_mg]
  upper := v2889_upper
  lower := (Primitive.Addresses.material2889 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2889_pa_checked.trans (by decide +kernel)
    · exact v2889_pb_checked.trans (by decide +kernel)
    · exact v2889_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 64 Primitive.Addresses.material2889
    · exact v2889_mb_checked.trans (by decide +kernel)
    · exact v2889_mg_checked.trans (by decide +kernel)
  upper_error := v2889_upper_checked
  lower_error := reuse_lower_error 36 64 Primitive.Addresses.material2889

def v2890_pa : Scalar.QComplex := ((999999288465583495387994481935 : Int)/10^30,(-1192924275353636242062555986 : Int)/10^30)
theorem v2890_pa_checked : Scalar.distance (sourceCoefficient 36 65 1 0) v2890_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2890_pb : Scalar.QComplex := ((-514719994236788975793139 : Int)/10^30,(-431477201554316796151125695 : Int)/10^30)
theorem v2890_pb_checked : Scalar.distance (sourceCoefficient 36 65 1 1) v2890_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2890_pg : Scalar.QComplex := ((-93086362321396890153696 : Int)/10^30,(111045060329940621116 : Int)/10^30)
theorem v2890_pg_checked : Scalar.distance (sourceCoefficient 36 65 1 2) v2890_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2890_mb : Scalar.QComplex := ((-887065194512615950281751 : Int)/10^30,(-431476596715462276836258392 : Int)/10^30)
theorem v2890_mb_checked : Scalar.distance (sourceCoefficient 36 65 3 1) v2890_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2890_mg : Scalar.QComplex := ((-93086231834204160097111 : Int)/10^30,(191374357212027423529 : Int)/10^30)
theorem v2890_mg_checked : Scalar.distance (sourceCoefficient 36 65 3 2) v2890_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2890_upper : Scalar.QComplex := ((999995740205033478519252082763 : Int)/10^30,(-2918830551297866056734045755 : Int)/10^30)
theorem v2890_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 65 5) 1) 14) v2890_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2890 : Material (36 : Basis) (65 : Basis) where
  plus := ![v2890_pa,v2890_pb,v2890_pg]
  minus := ![(Primitive.Addresses.material2890 1).one,v2890_mb,v2890_mg]
  upper := v2890_upper
  lower := (Primitive.Addresses.material2890 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2890_pa_checked.trans (by decide +kernel)
    · exact v2890_pb_checked.trans (by decide +kernel)
    · exact v2890_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 65 Primitive.Addresses.material2890
    · exact v2890_mb_checked.trans (by decide +kernel)
    · exact v2890_mg_checked.trans (by decide +kernel)
  upper_error := v2890_upper_checked
  lower_error := reuse_lower_error 36 65 Primitive.Addresses.material2890

def v2891_pa : Scalar.QComplex := ((999999267330287312478417416818 : Int)/10^30,(-1210511829173980139817647138 : Int)/10^30)
theorem v2891_pa_checked : Scalar.distance (sourceCoefficient 36 66 1 0) v2891_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2891_pb : Scalar.QComplex := ((-522308626840710731174759 : Int)/10^30,(-431477191360788187305048050 : Int)/10^30)
theorem v2891_pb_checked : Scalar.distance (sourceCoefficient 36 66 1 1) v2891_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2891_pg : Scalar.QComplex := ((-93086360238122592518389 : Int)/10^30,(112682222761849608881 : Int)/10^30)
theorem v2891_pg_checked : Scalar.distance (sourceCoefficient 36 66 1 2) v2891_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2891_mb : Scalar.QComplex := ((-894653815494386879631966 : Int)/10^30,(-431476579973289305647309909 : Int)/10^30)
theorem v2891_mb_checked : Scalar.distance (sourceCoefficient 36 66 3 1) v2891_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2891_mg : Scalar.QComplex := ((-93086228338133194481338 : Int)/10^30,(193011517236574124207 : Int)/10^30)
theorem v2891_mg_checked : Scalar.distance (sourceCoefficient 36 66 3 2) v2891_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2891_upper : Scalar.QComplex := ((999995688715246410656027592134 : Int)/10^30,(-2936418042446010685675802097 : Int)/10^30)
theorem v2891_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 66 5) 1) 14) v2891_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2891 : Material (36 : Basis) (66 : Basis) where
  plus := ![v2891_pa,v2891_pb,v2891_pg]
  minus := ![(Primitive.Addresses.material2891 1).one,v2891_mb,v2891_mg]
  upper := v2891_upper
  lower := (Primitive.Addresses.material2891 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2891_pa_checked.trans (by decide +kernel)
    · exact v2891_pb_checked.trans (by decide +kernel)
    · exact v2891_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 66 Primitive.Addresses.material2891
    · exact v2891_mb_checked.trans (by decide +kernel)
    · exact v2891_mg_checked.trans (by decide +kernel)
  upper_error := v2891_upper_checked
  lower_error := reuse_lower_error 36 66 Primitive.Addresses.material2891

def v2892_pa : Scalar.QComplex := ((999999231163791129055951884462 : Int)/10^30,(-1240028962013699107934619712 : Int)/10^30)
theorem v2892_pa_checked : Scalar.distance (sourceCoefficient 36 67 1 0) v2892_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2892_pb : Scalar.QComplex := ((-535044603387294892030719 : Int)/10^30,(-431477173853072953072775426 : Int)/10^30)
theorem v2892_pb_checked : Scalar.distance (sourceCoefficient 36 67 1 1) v2892_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2892_pg : Scalar.QComplex := ((-93086356666271107442496 : Int)/10^30,(115429866981174462103 : Int)/10^30)
theorem v2892_pg_checked : Scalar.distance (sourceCoefficient 36 67 1 2) v2892_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2892_mb : Scalar.QComplex := ((-907389772190415180392501 : Int)/10^30,(-431476551475006437725792342 : Int)/10^30)
theorem v2892_mb_checked : Scalar.distance (sourceCoefficient 36 67 3 1) v2892_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2892_mg : Scalar.QComplex := ((-93086222395189827393495 : Int)/10^30,(195759157350478499629 : Int)/10^30)
theorem v2892_mg_checked : Scalar.distance (sourceCoefficient 36 67 3 2) v2892_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2892_upper : Scalar.QComplex := ((999995601604910584999874856476 : Int)/10^30,(-2965935068903336201337919016 : Int)/10^30)
theorem v2892_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 67 5) 1) 14) v2892_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2892 : Material (36 : Basis) (67 : Basis) where
  plus := ![v2892_pa,v2892_pb,v2892_pg]
  minus := ![(Primitive.Addresses.material2892 1).one,v2892_mb,v2892_mg]
  upper := v2892_upper
  lower := (Primitive.Addresses.material2892 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2892_pa_checked.trans (by decide +kernel)
    · exact v2892_pb_checked.trans (by decide +kernel)
    · exact v2892_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 67 Primitive.Addresses.material2892
    · exact v2892_mb_checked.trans (by decide +kernel)
    · exact v2892_mg_checked.trans (by decide +kernel)
  upper_error := v2892_upper_checked
  lower_error := reuse_lower_error 36 67 Primitive.Addresses.material2892

def v2893_pa : Scalar.QComplex := ((999999168998215717000944440201 : Int)/10^30,(-1289186905767364916727359165 : Int)/10^30)
theorem v2893_pa_checked : Scalar.distance (sourceCoefficient 36 68 1 0) v2893_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2893_pb : Scalar.QComplex := ((-556255145894336490099507 : Int)/10^30,(-431477143583162065201457411 : Int)/10^30)
theorem v2893_pb_checked : Scalar.distance (sourceCoefficient 36 68 1 1) v2893_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2893_pg : Scalar.QComplex := ((-93086350507688689475554 : Int)/10^30,(120005803905220729448 : Int)/10^30)
theorem v2893_pg_checked : Scalar.distance (sourceCoefficient 36 68 1 2) v2893_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2893_mb : Scalar.QComplex := ((-928600280678232643354434 : Int)/10^30,(-431476502901363924521384998 : Int)/10^30)
theorem v2893_mb_checked : Scalar.distance (sourceCoefficient 36 68 3 1) v2893_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2893_mg : Scalar.QComplex := ((-93086212287782229644863 : Int)/10^30,(200335087256115065053 : Int)/10^30)
theorem v2893_mg_checked : Scalar.distance (sourceCoefficient 36 68 3 2) v2893_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2893_upper : Scalar.QComplex := ((999995454597276416260829863682 : Int)/10^30,(-3015092832149875742495250770 : Int)/10^30)
theorem v2893_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 68 5) 1) 14) v2893_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2893 : Material (36 : Basis) (68 : Basis) where
  plus := ![v2893_pa,v2893_pb,v2893_pg]
  minus := ![(Primitive.Addresses.material2893 1).one,v2893_mb,v2893_mg]
  upper := v2893_upper
  lower := (Primitive.Addresses.material2893 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2893_pa_checked.trans (by decide +kernel)
    · exact v2893_pb_checked.trans (by decide +kernel)
    · exact v2893_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 68 Primitive.Addresses.material2893
    · exact v2893_mb_checked.trans (by decide +kernel)
    · exact v2893_mg_checked.trans (by decide +kernel)
  upper_error := v2893_upper_checked
  lower_error := reuse_lower_error 36 68 Primitive.Addresses.material2893

def v2894_pa : Scalar.QComplex := ((999999140872112299584209105321 : Int)/10^30,(-1310822275253248874698507759 : Int)/10^30)
theorem v2894_pa_checked : Scalar.distance (sourceCoefficient 36 69 1 0) v2894_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2894_pb : Scalar.QComplex := ((-565590318945078081058968 : Int)/10^30,(-431477129820204622617103373 : Int)/10^30)
theorem v2894_pb_checked : Scalar.distance (sourceCoefficient 36 69 1 1) v2894_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2894_pg : Scalar.QComplex := ((-93086347714007653649584 : Int)/10^30,(122019762936071763706 : Int)/10^30)
theorem v2894_pg_checked : Scalar.distance (sourceCoefficient 36 69 1 2) v2894_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2894_mb : Scalar.QComplex := ((-937935438376250256680623 : Int)/10^30,(-431476481082577704311809250 : Int)/10^30)
theorem v2894_mb_checked : Scalar.distance (sourceCoefficient 36 69 3 1) v2894_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2894_mg : Scalar.QComplex := ((-93086207756146295757186 : Int)/10^30,(202349043126256198455 : Int)/10^30)
theorem v2894_mg_checked : Scalar.distance (sourceCoefficient 36 69 3 2) v2894_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2894_upper : Scalar.QComplex := ((999995389130529902123132944258 : Int)/10^30,(-3036728120869315401979410321 : Int)/10^30)
theorem v2894_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 69 5) 1) 14) v2894_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2894 : Material (36 : Basis) (69 : Basis) where
  plus := ![v2894_pa,v2894_pb,v2894_pg]
  minus := ![(Primitive.Addresses.material2894 1).one,v2894_mb,v2894_mg]
  upper := v2894_upper
  lower := (Primitive.Addresses.material2894 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2894_pa_checked.trans (by decide +kernel)
    · exact v2894_pb_checked.trans (by decide +kernel)
    · exact v2894_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 69 Primitive.Addresses.material2894
    · exact v2894_mb_checked.trans (by decide +kernel)
    · exact v2894_mg_checked.trans (by decide +kernel)
  upper_error := v2894_upper_checked
  lower_error := reuse_lower_error 36 69 Primitive.Addresses.material2894

def v2895_pa : Scalar.QComplex := ((999999122115259687694227647713 : Int)/10^30,(-1325054229057435321198741465 : Int)/10^30)
theorem v2895_pa_checked : Scalar.distance (sourceCoefficient 36 70 1 0) v2895_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2895_pb : Scalar.QComplex := ((-571731085333003137802366 : Int)/10^30,(-431477120619963497926739825 : Int)/10^30)
theorem v2895_pb_checked : Scalar.distance (sourceCoefficient 36 70 1 1) v2895_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2895_pg : Scalar.QComplex := ((-93086345848579076261256 : Int)/10^30,(123344564516473732293 : Int)/10^30)
theorem v2895_pg_checked : Scalar.distance (sourceCoefficient 36 70 1 2) v2895_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2895_mb : Scalar.QComplex := ((-944076194538293613181934 : Int)/10^30,(-431476466583135182363720915 : Int)/10^30)
theorem v2895_mb_checked : Scalar.distance (sourceCoefficient 36 70 3 1) v2895_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2895_mg : Scalar.QComplex := ((-93086204747474315914517 : Int)/10^30,(203673842603593145733 : Int)/10^30)
theorem v2895_mg_checked : Scalar.distance (sourceCoefficient 36 70 3 2) v2895_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2895_upper : Scalar.QComplex := ((999995345810644073099471922323 : Int)/10^30,(-3050960021104052460130115851 : Int)/10^30)
theorem v2895_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 70 5) 1) 14) v2895_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2895 : Material (36 : Basis) (70 : Basis) where
  plus := ![v2895_pa,v2895_pb,v2895_pg]
  minus := ![(Primitive.Addresses.material2895 1).one,v2895_mb,v2895_mg]
  upper := v2895_upper
  lower := (Primitive.Addresses.material2895 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2895_pa_checked.trans (by decide +kernel)
    · exact v2895_pb_checked.trans (by decide +kernel)
    · exact v2895_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 70 Primitive.Addresses.material2895
    · exact v2895_mb_checked.trans (by decide +kernel)
    · exact v2895_mg_checked.trans (by decide +kernel)
  upper_error := v2895_upper_checked
  lower_error := reuse_lower_error 36 70 Primitive.Addresses.material2895

def v2896_pa : Scalar.QComplex := ((999999089630890234158766705372 : Int)/10^30,(-1349347023845150981233050844 : Int)/10^30)
theorem v2896_pa_checked : Scalar.distance (sourceCoefficient 36 71 1 0) v2896_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2896_pb : Scalar.QComplex := ((-582212877040951594012349 : Int)/10^30,(-431477104646689341426973276 : Int)/10^30)
theorem v2896_pb_checked : Scalar.distance (sourceCoefficient 36 71 1 1) v2896_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2896_pg : Scalar.QComplex := ((-93086342613624822052869 : Int)/10^30,(125605893714050348478 : Int)/10^30)
theorem v2896_pg_checked : Scalar.distance (sourceCoefficient 36 71 1 2) v2896_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2896_mb : Scalar.QComplex := ((-954557968559175787479493 : Int)/10^30,(-431476441564552811858424343 : Int)/10^30)
theorem v2896_mb_checked : Scalar.distance (sourceCoefficient 36 71 3 1) v2896_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2896_mg : Scalar.QComplex := ((-93086199561096015205164 : Int)/10^30,(205935168167553729360 : Int)/10^30)
theorem v2896_mg_checked : Scalar.distance (sourceCoefficient 36 71 3 2) v2896_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2896_upper : Scalar.QComplex := ((999995271399163022747005131001 : Int)/10^30,(-3075252723645429198168677738 : Int)/10^30)
theorem v2896_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 36 71 5) 1) 14) v2896_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2896 : Material (36 : Basis) (71 : Basis) where
  plus := ![v2896_pa,v2896_pb,v2896_pg]
  minus := ![(Primitive.Addresses.material2896 1).one,v2896_mb,v2896_mg]
  upper := v2896_upper
  lower := (Primitive.Addresses.material2896 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2896_pa_checked.trans (by decide +kernel)
    · exact v2896_pb_checked.trans (by decide +kernel)
    · exact v2896_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 36 71 Primitive.Addresses.material2896
    · exact v2896_mb_checked.trans (by decide +kernel)
    · exact v2896_mg_checked.trans (by decide +kernel)
  upper_error := v2896_upper_checked
  lower_error := reuse_lower_error 36 71 Primitive.Addresses.material2896

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
