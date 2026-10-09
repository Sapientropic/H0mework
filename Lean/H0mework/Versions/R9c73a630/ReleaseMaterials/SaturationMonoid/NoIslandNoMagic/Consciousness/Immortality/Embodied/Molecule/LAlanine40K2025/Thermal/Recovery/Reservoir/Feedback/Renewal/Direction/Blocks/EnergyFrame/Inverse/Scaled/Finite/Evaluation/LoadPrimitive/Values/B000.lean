import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B000

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1_pa : Scalar.QComplex := ((999905766751237686521706461288 : Int)/10^30,(13727986655713745139741298626 : Int)/10^30)
theorem v1_pa_checked : Scalar.distance (sourceCoefficient 0 2 1 0) v1_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1_pb : Scalar.QComplex := ((5923313857994148359120675 : Int)/10^30,(-431436585234496279596506106 : Int)/10^30)
theorem v1_pb_checked : Scalar.distance (sourceCoefficient 0 2 1 1) v1_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1_pg : Scalar.QComplex := ((-93077628262691103622970 : Int)/10^30,(-1277888858354387907523 : Int)/10^30)
theorem v1_pg_checked : Scalar.distance (sourceCoefficient 0 2 1 2) v1_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1_mb : Scalar.QComplex := ((5551001310598799484167312 : Int)/10^30,(-431441536144021266760116093 : Int)/10^30)
theorem v1_mb_checked : Scalar.distance (sourceCoefficient 0 2 3 1) v1_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1_mg : Scalar.QComplex := ((-93078696366167025827192 : Int)/10^30,(-1197566581408021455154 : Int)/10^30)
theorem v1_mg_checked : Scalar.distance (sourceCoefficient 0 2 3 2) v1_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1_upper : Scalar.QComplex := ((999927970768629833828529546234 : Int)/10^30,(12002219566820154036738415810 : Int)/10^30)
theorem v1_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 2 5) 1) 14) v1_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1 : Material (0 : Basis) (2 : Basis) where
  plus := ![v1_pa,v1_pb,v1_pg]
  minus := ![(Primitive.Addresses.material1 1).one,v1_mb,v1_mg]
  upper := v1_upper
  lower := (Primitive.Addresses.material1 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1_pa_checked.trans (by decide +kernel)
    · exact v1_pb_checked.trans (by decide +kernel)
    · exact v1_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 2 Primitive.Addresses.material1
    · exact v1_mb_checked.trans (by decide +kernel)
    · exact v1_mg_checked.trans (by decide +kernel)
  upper_error := v1_upper_checked
  lower_error := reuse_lower_error 0 2 Primitive.Addresses.material1

def v2_pa : Scalar.QComplex := ((999928920574206329875504032681 : Int)/10^30,(11922826816764935763935778670 : Int)/10^30)
theorem v2_pa_checked : Scalar.distance (sourceCoefficient 0 3 1 0) v2_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2_pb : Scalar.QComplex := ((5144419602252514431276461 : Int)/10^30,(-431445832344724068022408708 : Int)/10^30)
theorem v2_pb_checked : Scalar.distance (sourceCoefficient 0 3 1 1) v2_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2_pg : Scalar.QComplex := ((-93079703396122883573072 : Int)/10^30,(-1109852071395770907496 : Int)/10^30)
theorem v2_pg_checked : Scalar.distance (sourceCoefficient 0 3 1 2) v2_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2_mb : Scalar.QComplex := ((4772099365035441997951619 : Int)/10^30,(-431450111100143323448581468 : Int)/10^30)
theorem v2_mb_checked : Scalar.distance (sourceCoefficient 0 3 3 1) v2_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2_mg : Scalar.QComplex := ((-93080626490647089419576 : Int)/10^30,(-1029528066270488814619 : Int)/10^30)
theorem v2_mg_checked : Scalar.distance (sourceCoefficient 0 3 3 2) v2_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2_upper : Scalar.QComplex := ((999948009014994373409132923866 : Int)/10^30,(10197022455046930337967334187 : Int)/10^30)
theorem v2_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 3 5) 1) 14) v2_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2 : Material (0 : Basis) (3 : Basis) where
  plus := ![v2_pa,v2_pb,v2_pg]
  minus := ![(Primitive.Addresses.material2 1).one,v2_mb,v2_mg]
  upper := v2_upper
  lower := (Primitive.Addresses.material2 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2_pa_checked.trans (by decide +kernel)
    · exact v2_pb_checked.trans (by decide +kernel)
    · exact v2_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 3 Primitive.Addresses.material2
    · exact v2_mb_checked.trans (by decide +kernel)
    · exact v2_mg_checked.trans (by decide +kernel)
  upper_error := v2_upper_checked
  lower_error := reuse_lower_error 0 3 Primitive.Addresses.material2

def v3_pa : Scalar.QComplex := ((999928984316855450719232402228 : Int)/10^30,(11917479727771559105030966193 : Int)/10^30)
theorem v3_pa_checked : Scalar.distance (sourceCoefficient 0 4 1 0) v3_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3_pb : Scalar.QComplex := ((5142112424464168137085975 : Int)/10^30,(-431445856950409961487500147 : Int)/10^30)
theorem v3_pb_checked : Scalar.distance (sourceCoefficient 0 4 1 1) v3_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3_pg : Scalar.QComplex := ((-93079709017110769460175 : Int)/10^30,(-1109354326833662642291 : Int)/10^30)
theorem v3_pg_checked : Scalar.distance (sourceCoefficient 0 4 1 2) v3_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3_mb : Scalar.QComplex := ((4769792166872564710490376 : Int)/10^30,(-431450133714829535179640995 : Int)/10^30)
theorem v3_mb_checked : Scalar.distance (sourceCoefficient 0 4 3 1) v3_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3_mg : Scalar.QComplex := ((-93080631682101742839463 : Int)/10^30,(-1029030317043054212314 : Int)/10^30)
theorem v3_mg_checked : Scalar.distance (sourceCoefficient 0 4 3 2) v3_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3_upper : Scalar.QComplex := ((999948063528958038620829978750 : Int)/10^30,(10191675264003384926881436058 : Int)/10^30)
theorem v3_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 4 5) 1) 14) v3_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3 : Material (0 : Basis) (4 : Basis) where
  plus := ![v3_pa,v3_pb,v3_pg]
  minus := ![(Primitive.Addresses.material3 1).one,v3_mb,v3_mg]
  upper := v3_upper
  lower := (Primitive.Addresses.material3 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3_pa_checked.trans (by decide +kernel)
    · exact v3_pb_checked.trans (by decide +kernel)
    · exact v3_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 4 Primitive.Addresses.material3
    · exact v3_mb_checked.trans (by decide +kernel)
    · exact v3_mg_checked.trans (by decide +kernel)
  upper_error := v3_upper_checked
  lower_error := reuse_lower_error 0 4 Primitive.Addresses.material3

def v4_pa : Scalar.QComplex := ((999929280244647644930755407212 : Int)/10^30,(11892624160416112365210248986 : Int)/10^30)
theorem v4_pa_checked : Scalar.distance (sourceCoefficient 0 5 1 0) v4_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4_pb : Scalar.QComplex := ((5131387670444169905998637 : Int)/10^30,(-431445971112229952081813991 : Int)/10^30)
theorem v4_pb_checked : Scalar.distance (sourceCoefficient 0 5 1 1) v4_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4_pg : Scalar.QComplex := ((-93079735105106272175467 : Int)/10^30,(-1107040596196246744437 : Int)/10^30)
theorem v4_pg_checked : Scalar.distance (sourceCoefficient 0 5 1 2) v4_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4_mb : Scalar.QComplex := ((4759067318329373552142957 : Int)/10^30,(-431450238621627323842776230 : Int)/10^30)
theorem v4_mb_checked : Scalar.distance (sourceCoefficient 0 5 3 1) v4_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4_mg : Scalar.QComplex := ((-93080655773442198271408 : Int)/10^30,(-1026716564754380814341 : Int)/10^30)
theorem v4_mg_checked : Scalar.distance (sourceCoefficient 0 5 3 2) v4_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4_upper : Scalar.QComplex := ((999948316557855107103261603674 : Int)/10^30,(10166819222922863055343033243 : Int)/10^30)
theorem v4_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 5 5) 1) 14) v4_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4 : Material (0 : Basis) (5 : Basis) where
  plus := ![v4_pa,v4_pb,v4_pg]
  minus := ![(Primitive.Addresses.material4 1).one,v4_mb,v4_mg]
  upper := v4_upper
  lower := (Primitive.Addresses.material4 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4_pa_checked.trans (by decide +kernel)
    · exact v4_pb_checked.trans (by decide +kernel)
    · exact v4_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 5 Primitive.Addresses.material4
    · exact v4_mb_checked.trans (by decide +kernel)
    · exact v4_mg_checked.trans (by decide +kernel)
  upper_error := v4_upper_checked
  lower_error := reuse_lower_error 0 5 Primitive.Addresses.material4

def v5_pa : Scalar.QComplex := ((999967531716728594695759546288 : Int)/10^30,(8058257401783093715782942110 : Int)/10^30)
theorem v5_pa_checked : Scalar.distance (sourceCoefficient 0 6 1 0) v5_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v5_pb : Scalar.QComplex := ((3476923190386881023917912 : Int)/10^30,(-431459325175004984707181511 : Int)/10^30)
theorem v5_pb_checked : Scalar.distance (sourceCoefficient 0 6 1 1) v5_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v5_pg : Scalar.QComplex := ((-93082955945727650983250 : Int)/10^30,(-750110773538589659597 : Int)/10^30)
theorem v5_pg_checked : Scalar.distance (sourceCoefficient 0 6 1 2) v5_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v5_mb : Scalar.QComplex := ((3104591930350093165032231 : Int)/10^30,(-431462164951098053226294980 : Int)/10^30)
theorem v5_mb_checked : Scalar.distance (sourceCoefficient 0 6 3 1) v5_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v5_mg : Scalar.QComplex := ((-93083568598502879819156 : Int)/10^30,(-669784095557614230444 : Int)/10^30)
theorem v5_mg_checked : Scalar.distance (sourceCoefficient 0 6 3 2) v5_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v5_upper : Scalar.QComplex := ((999979950203790617027072688906 : Int)/10^30,(6332392156558049750897391803 : Int)/10^30)
theorem v5_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 6 5) 1) 14) v5_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material5 : Material (0 : Basis) (6 : Basis) where
  plus := ![v5_pa,v5_pb,v5_pg]
  minus := ![(Primitive.Addresses.material5 1).one,v5_mb,v5_mg]
  upper := v5_upper
  lower := (Primitive.Addresses.material5 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v5_pa_checked.trans (by decide +kernel)
    · exact v5_pb_checked.trans (by decide +kernel)
    · exact v5_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 6 Primitive.Addresses.material5
    · exact v5_mb_checked.trans (by decide +kernel)
    · exact v5_mg_checked.trans (by decide +kernel)
  upper_error := v5_upper_checked
  lower_error := reuse_lower_error 0 6 Primitive.Addresses.material5

def v6_pa : Scalar.QComplex := ((999968009078106148851885757129 : Int)/10^30,(7998801183216062268309408809 : Int)/10^30)
theorem v6_pa_checked : Scalar.distance (sourceCoefficient 0 7 1 0) v6_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v6_pb : Scalar.QComplex := ((3451268893563877102085093 : Int)/10^30,(-431459465642408668327947206 : Int)/10^30)
theorem v6_pb_checked : Scalar.distance (sourceCoefficient 0 7 1 1) v6_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v6_pg : Scalar.QComplex := ((-93082993315779587267962 : Int)/10^30,(-744576176749865005122 : Int)/10^30)
theorem v6_pg_checked : Scalar.distance (sourceCoefficient 0 7 1 2) v6_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v6_mb : Scalar.QComplex := ((3078937521862313447738798 : Int)/10^30,(-431462283279946702798062418 : Int)/10^30)
theorem v6_mb_checked : Scalar.distance (sourceCoefficient 0 7 3 1) v6_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v6_mg : Scalar.QComplex := ((-93083601192433141842325 : Int)/10^30,(-664249468581001167627 : Int)/10^30)
theorem v6_mg_checked : Scalar.distance (sourceCoefficient 0 7 3 2) v6_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v6_upper : Scalar.QComplex := ((999980324948417776804004623334 : Int)/10^30,(6272935202661639868380980333 : Int)/10^30)
theorem v6_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 7 5) 1) 14) v6_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material6 : Material (0 : Basis) (7 : Basis) where
  plus := ![v6_pa,v6_pb,v6_pg]
  minus := ![(Primitive.Addresses.material6 1).one,v6_mb,v6_mg]
  upper := v6_upper
  lower := (Primitive.Addresses.material6 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v6_pa_checked.trans (by decide +kernel)
    · exact v6_pb_checked.trans (by decide +kernel)
    · exact v6_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 7 Primitive.Addresses.material6
    · exact v6_mb_checked.trans (by decide +kernel)
    · exact v6_mg_checked.trans (by decide +kernel)
  upper_error := v6_upper_checked
  lower_error := reuse_lower_error 0 7 Primitive.Addresses.material6

def v7_pa : Scalar.QComplex := ((999968314953824536436335358185 : Int)/10^30,(7960470363538575857379314909 : Int)/10^30)
theorem v7_pa_checked : Scalar.distance (sourceCoefficient 0 8 1 0) v7_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v7_pb : Scalar.QComplex := ((3434729831187784197296151 : Int)/10^30,(-431459555122033066020029830 : Int)/10^30)
theorem v7_pb_checked : Scalar.distance (sourceCoefficient 0 8 1 1) v7_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v7_pg : Scalar.QComplex := ((-93083017204321935810724 : Int)/10^30,(-741008078678945485255 : Int)/10^30)
theorem v7_pg_checked : Scalar.distance (sourceCoefficient 0 8 1 2) v7_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v7_mb : Scalar.QComplex := ((3062398388427583495534193 : Int)/10^30,(-431462358487071844286122976 : Int)/10^30)
theorem v7_mb_checked : Scalar.distance (sourceCoefficient 0 8 3 1) v7_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v7_mg : Scalar.QComplex := ((-93083622001858661557071 : Int)/10^30,(-660681351223911482917 : Int)/10^30)
theorem v7_mg_checked : Scalar.distance (sourceCoefficient 0 8 3 2) v7_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v7_upper : Scalar.QComplex := ((999980564668163179892671225724 : Int)/10^30,(6234603912159665604132769032 : Int)/10^30)
theorem v7_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 8 5) 1) 14) v7_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material7 : Material (0 : Basis) (8 : Basis) where
  plus := ![v7_pa,v7_pb,v7_pg]
  minus := ![(Primitive.Addresses.material7 1).one,v7_mb,v7_mg]
  upper := v7_upper
  lower := (Primitive.Addresses.material7 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v7_pa_checked.trans (by decide +kernel)
    · exact v7_pb_checked.trans (by decide +kernel)
    · exact v7_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 8 Primitive.Addresses.material7
    · exact v7_mb_checked.trans (by decide +kernel)
    · exact v7_mg_checked.trans (by decide +kernel)
  upper_error := v7_upper_checked
  lower_error := reuse_lower_error 0 8 Primitive.Addresses.material7

def v8_pa : Scalar.QComplex := ((999968483165423211198834028165 : Int)/10^30,(7939312050972417954076170502 : Int)/10^30)
theorem v8_pa_checked : Scalar.distance (sourceCoefficient 0 9 1 0) v8_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v8_pb : Scalar.QComplex := ((3425600398832791301989169 : Int)/10^30,(-431459604151991486671522982 : Int)/10^30)
theorem v8_pb_checked : Scalar.distance (sourceCoefficient 0 9 1 1) v8_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v8_pg : Scalar.QComplex := ((-93083030322256957442772 : Int)/10^30,(-739038516533197107496 : Int)/10^30)
theorem v8_pg_checked : Scalar.distance (sourceCoefficient 0 9 1 2) v8_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v8_mb : Scalar.QComplex := ((3053268917161249611993324 : Int)/10^30,(-431462399638723060854206480 : Int)/10^30)
theorem v8_mb_checked : Scalar.distance (sourceCoefficient 0 9 3 1) v8_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v8_mg : Scalar.QComplex := ((-93083633420145372787671 : Int)/10^30,(-658711778491333991649 : Int)/10^30)
theorem v8_mg_checked : Scalar.distance (sourceCoefficient 0 9 3 2) v8_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v8_upper : Scalar.QComplex := ((999980696362183301171872684728 : Int)/10^30,(6213445340788369562522700945 : Int)/10^30)
theorem v8_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 9 5) 1) 14) v8_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material8 : Material (0 : Basis) (9 : Basis) where
  plus := ![v8_pa,v8_pb,v8_pg]
  minus := ![(Primitive.Addresses.material8 1).one,v8_mb,v8_mg]
  upper := v8_upper
  lower := (Primitive.Addresses.material8 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v8_pa_checked.trans (by decide +kernel)
    · exact v8_pb_checked.trans (by decide +kernel)
    · exact v8_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 9 Primitive.Addresses.material8
    · exact v8_mb_checked.trans (by decide +kernel)
    · exact v8_mg_checked.trans (by decide +kernel)
  upper_error := v8_upper_checked
  lower_error := reuse_lower_error 0 9 Primitive.Addresses.material8

def v9_pa : Scalar.QComplex := ((999968814747473525584673665511 : Int)/10^30,(7897438352590901400772063209 : Int)/10^30)
theorem v9_pa_checked : Scalar.distance (sourceCoefficient 0 10 1 0) v9_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v9_pb : Scalar.QComplex := ((3407532650509711725813417 : Int)/10^30,(-431459700426232998900699960 : Int)/10^30)
theorem v9_pb_checked : Scalar.distance (sourceCoefficient 0 10 1 1) v9_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v9_pg : Scalar.QComplex := ((-93083056140184736289674 : Int)/10^30,(-735140623083840272306 : Int)/10^30)
theorem v9_pg_checked : Scalar.distance (sourceCoefficient 0 10 1 2) v9_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v9_mb : Scalar.QComplex := ((3035201092485284079213592 : Int)/10^30,(-431462480321275664142623115 : Int)/10^30)
theorem v9_mb_checked : Scalar.distance (sourceCoefficient 0 10 3 1) v9_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v9_mg : Scalar.QComplex := ((-93083655874357046249241 : Int)/10^30,(-654813864213632153344 : Int)/10^30)
theorem v9_mg_checked : Scalar.distance (sourceCoefficient 0 10 3 2) v9_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v9_upper : Scalar.QComplex := ((999980955673535108789508918715 : Int)/10^30,(6171571132492269964342190328 : Int)/10^30)
theorem v9_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 10 5) 1) 14) v9_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material9 : Material (0 : Basis) (10 : Basis) where
  plus := ![v9_pa,v9_pb,v9_pg]
  minus := ![(Primitive.Addresses.material9 1).one,v9_mb,v9_mg]
  upper := v9_upper
  lower := (Primitive.Addresses.material9 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v9_pa_checked.trans (by decide +kernel)
    · exact v9_pb_checked.trans (by decide +kernel)
    · exact v9_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 10 Primitive.Addresses.material9
    · exact v9_mb_checked.trans (by decide +kernel)
    · exact v9_mg_checked.trans (by decide +kernel)
  upper_error := v9_upper_checked
  lower_error := reuse_lower_error 0 10 Primitive.Addresses.material9

def v10_pa : Scalar.QComplex := ((999968885886506570669238907202 : Int)/10^30,(7888425628653678289112545675 : Int)/10^30)
theorem v10_pa_checked : Scalar.distance (sourceCoefficient 0 11 1 0) v10_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v10_pb : Scalar.QComplex := ((3403643822354345289425733 : Int)/10^30,(-431459721015972731745737601 : Int)/10^30)
theorem v10_pb_checked : Scalar.distance (sourceCoefficient 0 11 1 1) v10_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v10_pg : Scalar.QComplex := ((-93083061672224412578996 : Int)/10^30,(-734301656433802662943 : Int)/10^30)
theorem v10_pg_checked : Scalar.distance (sourceCoefficient 0 11 1 2) v10_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v10_mb : Scalar.QComplex := ((3031312248009888031303771 : Int)/10^30,(-431462497555124178723706772 : Int)/10^30)
theorem v10_mb_checked : Scalar.distance (sourceCoefficient 0 11 3 1) v10_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v10_mg : Scalar.QComplex := ((-93083660682404229380156 : Int)/10^30,(-653974893102079083639 : Int)/10^30)
theorem v10_mg_checked : Scalar.distance (sourceCoefficient 0 11 3 2) v10_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v10_upper : Scalar.QComplex := ((999981011257318312922466629962 : Int)/10^30,(6162558299198923095101073840 : Int)/10^30)
theorem v10_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 11 5) 1) 14) v10_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material10 : Material (0 : Basis) (11 : Basis) where
  plus := ![v10_pa,v10_pb,v10_pg]
  minus := ![(Primitive.Addresses.material10 1).one,v10_mb,v10_mg]
  upper := v10_upper
  lower := (Primitive.Addresses.material10 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v10_pa_checked.trans (by decide +kernel)
    · exact v10_pb_checked.trans (by decide +kernel)
    · exact v10_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 11 Primitive.Addresses.material10
    · exact v10_mb_checked.trans (by decide +kernel)
    · exact v10_mg_checked.trans (by decide +kernel)
  upper_error := v10_upper_checked
  lower_error := reuse_lower_error 0 11 Primitive.Addresses.material10

def v11_pa : Scalar.QComplex := ((999968924695689595804538620608 : Int)/10^30,(7883504483811143663018755637 : Int)/10^30)
theorem v11_pa_checked : Scalar.distance (sourceCoefficient 0 12 1 0) v11_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v11_pb : Scalar.QComplex := ((3401520436970411825860274 : Int)/10^30,(-431459732238695941844625186 : Int)/10^30)
theorem v11_pb_checked : Scalar.distance (sourceCoefficient 0 12 1 1) v11_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v11_pg : Scalar.QComplex := ((-93083064689115610540870 : Int)/10^30,(-733843562255538976981 : Int)/10^30)
theorem v11_pg_checked : Scalar.distance (sourceCoefficient 0 12 1 2) v11_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v11_mb : Scalar.QComplex := ((3029188853731883312057591 : Int)/10^30,(-431462506945457257482861914 : Int)/10^30)
theorem v11_mb_checked : Scalar.distance (sourceCoefficient 0 12 3 1) v11_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v11_mg : Scalar.QComplex := ((-93083663303979659969898 : Int)/10^30,(-653516796490943568078 : Int)/10^30)
theorem v11_mg_checked : Scalar.distance (sourceCoefficient 0 12 3 2) v11_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v11_upper : Scalar.QComplex := ((999981041572993980896427831076 : Int)/10^30,(6157637094704726473879609849 : Int)/10^30)
theorem v11_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 12 5) 1) 14) v11_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material11 : Material (0 : Basis) (12 : Basis) where
  plus := ![v11_pa,v11_pb,v11_pg]
  minus := ![(Primitive.Addresses.material11 1).one,v11_mb,v11_mg]
  upper := v11_upper
  lower := (Primitive.Addresses.material11 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v11_pa_checked.trans (by decide +kernel)
    · exact v11_pb_checked.trans (by decide +kernel)
    · exact v11_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 12 Primitive.Addresses.material11
    · exact v11_mb_checked.trans (by decide +kernel)
    · exact v11_mg_checked.trans (by decide +kernel)
  upper_error := v11_upper_checked
  lower_error := reuse_lower_error 0 12 Primitive.Addresses.material11

def v12_pa : Scalar.QComplex := ((999969329489010987130700509208 : Int)/10^30,(7831990889791778316264367089 : Int)/10^30)
theorem v12_pa_checked : Scalar.distance (sourceCoefficient 0 13 1 0) v12_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v12_pb : Scalar.QComplex := ((3379293250387361133463849 : Int)/10^30,(-431459848879679854566915906 : Int)/10^30)
theorem v12_pb_checked : Scalar.distance (sourceCoefficient 0 13 1 1) v12_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v12_pg : Scalar.QComplex := ((-93083096111476676293426 : Int)/10^30,(-729048321023239298821 : Int)/10^30)
theorem v12_pg_checked : Scalar.distance (sourceCoefficient 0 13 1 2) v12_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v12_mb : Scalar.QComplex := ((3006961574769114215364809 : Int)/10^30,(-431462604405336793585375929 : Int)/10^30)
theorem v12_mb_checked : Scalar.distance (sourceCoefficient 0 13 3 1) v12_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v12_mg : Scalar.QComplex := ((-93083690588251811914667 : Int)/10^30,(-648721529928048964917 : Int)/10^30)
theorem v12_mg_checked : Scalar.distance (sourceCoefficient 0 13 3 2) v12_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v12_upper : Scalar.QComplex := ((999981357457922479439954874950 : Int)/10^30,(6106122878772258048968687918 : Int)/10^30)
theorem v12_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 13 5) 1) 14) v12_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material12 : Material (0 : Basis) (13 : Basis) where
  plus := ![v12_pa,v12_pb,v12_pg]
  minus := ![(Primitive.Addresses.material12 1).one,v12_mb,v12_mg]
  upper := v12_upper
  lower := (Primitive.Addresses.material12 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v12_pa_checked.trans (by decide +kernel)
    · exact v12_pb_checked.trans (by decide +kernel)
    · exact v12_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 13 Primitive.Addresses.material12
    · exact v12_mb_checked.trans (by decide +kernel)
    · exact v12_mg_checked.trans (by decide +kernel)
  upper_error := v12_upper_checked
  lower_error := reuse_lower_error 0 13 Primitive.Addresses.material12

def v13_pa : Scalar.QComplex := ((999969457098377896708666816850 : Int)/10^30,(7815681056399825044392235055 : Int)/10^30)
theorem v13_pa_checked : Scalar.distance (sourceCoefficient 0 14 1 0) v13_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v13_pb : Scalar.QComplex := ((3372255852110450987886778 : Int)/10^30,(-431459885491418260403268311 : Int)/10^30)
theorem v13_pb_checked : Scalar.distance (sourceCoefficient 0 14 1 1) v13_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v13_pg : Scalar.QComplex := ((-93083106000108501022466 : Int)/10^30,(-727530089115843887635 : Int)/10^30)
theorem v13_pg_checked : Scalar.distance (sourceCoefficient 0 14 1 2) v13_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v13_mb : Scalar.QComplex := ((2999924147518267760521049 : Int)/10^30,(-431462634944103806877381615 : Int)/10^30)
theorem v13_mb_checked : Scalar.distance (sourceCoefficient 0 14 3 1) v13_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v13_mg : Scalar.QComplex := ((-93083699166714197198681 : Int)/10^30,(-647203290052516782183 : Int)/10^30)
theorem v13_mg_checked : Scalar.distance (sourceCoefficient 0 14 3 2) v13_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v13_upper : Scalar.QComplex := ((999981456917806511871799327649 : Int)/10^30,(6089812849429695072199756849 : Int)/10^30)
theorem v13_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 14 5) 1) 14) v13_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material13 : Material (0 : Basis) (14 : Basis) where
  plus := ![v13_pa,v13_pb,v13_pg]
  minus := ![(Primitive.Addresses.material13 1).one,v13_mb,v13_mg]
  upper := v13_upper
  lower := (Primitive.Addresses.material13 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v13_pa_checked.trans (by decide +kernel)
    · exact v13_pb_checked.trans (by decide +kernel)
    · exact v13_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 14 Primitive.Addresses.material13
    · exact v13_mb_checked.trans (by decide +kernel)
    · exact v13_mg_checked.trans (by decide +kernel)
  upper_error := v13_upper_checked
  lower_error := reuse_lower_error 0 14 Primitive.Addresses.material13

def v14_pa : Scalar.QComplex := ((999969662134988379830069210734 : Int)/10^30,(7789403676610095714207077255 : Int)/10^30)
theorem v14_pa_checked : Scalar.distance (sourceCoefficient 0 15 1 0) v14_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v14_pb : Scalar.QComplex := ((3360917638384534262886870 : Int)/10^30,(-431459944156022183905701529 : Int)/10^30)
theorem v14_pb_checked : Scalar.distance (sourceCoefficient 0 15 1 1) v14_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v14_pg : Scalar.QComplex := ((-93083121871279663265761 : Int)/10^30,(-725084009235285686035 : Int)/10^30)
theorem v14_pg_checked : Scalar.distance (sourceCoefficient 0 15 1 2) v14_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v14_mb : Scalar.QComplex := ((2988585887389175157342607 : Int)/10^30,(-431462683824318095590376300 : Int)/10^30)
theorem v14_mb_checked : Scalar.distance (sourceCoefficient 0 15 3 1) v14_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v14_mg : Scalar.QComplex := ((-93083712927022680306092 : Int)/10^30,(-644757197386640009486 : Int)/10^30)
theorem v14_mg_checked : Scalar.distance (sourceCoefficient 0 15 3 2) v14_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v14_upper : Scalar.QComplex := ((999981616601737965247146044039 : Int)/10^30,(6063535154902447263087621282 : Int)/10^30)
theorem v14_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 15 5) 1) 14) v14_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material14 : Material (0 : Basis) (15 : Basis) where
  plus := ![v14_pa,v14_pb,v14_pg]
  minus := ![(Primitive.Addresses.material14 1).one,v14_mb,v14_mg]
  upper := v14_upper
  lower := (Primitive.Addresses.material14 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v14_pa_checked.trans (by decide +kernel)
    · exact v14_pb_checked.trans (by decide +kernel)
    · exact v14_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 15 Primitive.Addresses.material14
    · exact v14_mb_checked.trans (by decide +kernel)
    · exact v14_mg_checked.trans (by decide +kernel)
  upper_error := v14_upper_checked
  lower_error := reuse_lower_error 0 15 Primitive.Addresses.material14

def v15_pa : Scalar.QComplex := ((999969688087295677477498373905 : Int)/10^30,(7786071319773101753071359079 : Int)/10^30)
theorem v15_pa_checked : Scalar.distance (sourceCoefficient 0 16 1 0) v15_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v15_pb : Scalar.QComplex := ((3359479786785853260547290 : Int)/10^30,(-431459951567168765460678581 : Int)/10^30)
theorem v15_pb_checked : Scalar.distance (sourceCoefficient 0 16 1 1) v15_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v15_pg : Scalar.QComplex := ((-93083123878618460064697 : Int)/10^30,(-724773810466671200440 : Int)/10^30)
theorem v15_pg_checked : Scalar.distance (sourceCoefficient 0 16 1 2) v15_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v15_mb : Scalar.QComplex := ((2987148029930386304025697 : Int)/10^30,(-431462689994660746407128485 : Int)/10^30)
theorem v15_mb_checked : Scalar.distance (sourceCoefficient 0 16 3 1) v15_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v15_mg : Scalar.QComplex := ((-93083714666673163200670 : Int)/10^30,(-644446997001283727777 : Int)/10^30)
theorem v15_mg_checked : Scalar.distance (sourceCoefficient 0 16 3 2) v15_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v15_upper : Scalar.QComplex := ((999981636802661018380593990357 : Int)/10^30,(6060202758237279343709956118 : Int)/10^30)
theorem v15_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 16 5) 1) 14) v15_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material15 : Material (0 : Basis) (16 : Basis) where
  plus := ![v15_pa,v15_pb,v15_pg]
  minus := ![(Primitive.Addresses.material15 1).one,v15_mb,v15_mg]
  upper := v15_upper
  lower := (Primitive.Addresses.material15 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v15_pa_checked.trans (by decide +kernel)
    · exact v15_pb_checked.trans (by decide +kernel)
    · exact v15_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 16 Primitive.Addresses.material15
    · exact v15_mb_checked.trans (by decide +kernel)
    · exact v15_mg_checked.trans (by decide +kernel)
  upper_error := v15_upper_checked
  lower_error := reuse_lower_error 0 16 Primitive.Addresses.material15

def v16_pa : Scalar.QComplex := ((999969740164963396020662019181 : Int)/10^30,(7779380079131724503005397171 : Int)/10^30)
theorem v16_pa_checked : Scalar.distance (sourceCoefficient 0 17 1 0) v16_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v16_pb : Scalar.QComplex := ((3356592637721378753785486 : Int)/10^30,(-431459966429163381643826727 : Int)/10^30)
theorem v16_pb_checked : Scalar.distance (sourceCoefficient 0 17 1 1) v16_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v16_pg : Scalar.QComplex := ((-93083127905633063732585 : Int)/10^30,(-724150943620447732504 : Int)/10^30)
theorem v16_pg_checked : Scalar.distance (sourceCoefficient 0 17 1 2) v16_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v16_mb : Scalar.QComplex := ((2984260869115697348822090 : Int)/10^30,(-431462702365170218515790561 : Int)/10^30)
theorem v16_mb_checked : Scalar.distance (sourceCoefficient 0 17 3 1) v16_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v16_mg : Scalar.QComplex := ((-93083718156180232017506 : Int)/10^30,(-643824126911849820150 : Int)/10^30)
theorem v16_mg_checked : Scalar.distance (sourceCoefficient 0 17 3 2) v16_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v16_upper : Scalar.QComplex := ((999981677331776850947199551498 : Int)/10^30,(6053511437680388987540152241 : Int)/10^30)
theorem v16_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 0 17 5) 1) 14) v16_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material16 : Material (0 : Basis) (17 : Basis) where
  plus := ![v16_pa,v16_pb,v16_pg]
  minus := ![(Primitive.Addresses.material16 1).one,v16_mb,v16_mg]
  upper := v16_upper
  lower := (Primitive.Addresses.material16 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v16_pa_checked.trans (by decide +kernel)
    · exact v16_pb_checked.trans (by decide +kernel)
    · exact v16_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 0 17 Primitive.Addresses.material16
    · exact v16_mb_checked.trans (by decide +kernel)
    · exact v16_mg_checked.trans (by decide +kernel)
  upper_error := v16_upper_checked
  lower_error := reuse_lower_error 0 17 Primitive.Addresses.material16

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
