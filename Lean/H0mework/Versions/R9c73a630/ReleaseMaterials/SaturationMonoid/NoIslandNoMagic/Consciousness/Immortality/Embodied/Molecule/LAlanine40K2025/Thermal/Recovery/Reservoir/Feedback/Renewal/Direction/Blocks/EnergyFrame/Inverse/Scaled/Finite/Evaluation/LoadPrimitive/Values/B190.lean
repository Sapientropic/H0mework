import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B126
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B127

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3041_pa : Scalar.QComplex := ((999998021182713117096750176020 : Int)/10^30,(-1989379465574115056451567882 : Int)/10^30)
theorem v3041_pa_checked : Scalar.distance (sourceCoefficient 38 97 1 0) v3041_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3041_pb : Scalar.QComplex := ((-858372330309064139533113 : Int)/10^30,(-431476571765729544030826931 : Int)/10^30)
theorem v3041_pb_checked : Scalar.distance (sourceCoefficient 38 97 1 1) v3041_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3041_pg : Scalar.QComplex := ((-93086235403069955747373 : Int)/10^30,(185184211684184915664 : Int)/10^30)
theorem v3041_pg_checked : Scalar.distance (sourceCoefficient 38 97 1 2) v3041_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3041_mb : Scalar.QComplex := ((-1230716859148234533124110 : Int)/10^30,(-431475670370621020080186039 : Int)/10^30)
theorem v3041_mb_checked : Scalar.distance (sourceCoefficient 38 97 3 1) v3041_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3041_mg : Scalar.QComplex := ((-93086040937175967895182 : Int)/10^30,(265513371436077387145 : Int)/10^30)
theorem v3041_mg_checked : Scalar.distance (sourceCoefficient 38 97 3 2) v3041_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3041_upper : Scalar.QComplex := ((999993098314646099092195863499 : Int)/10^30,(-3715282368076629967465251784 : Int)/10^30)
theorem v3041_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 38 97 5) 1) 14) v3041_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3041 : Material (38 : Basis) (97 : Basis) where
  plus := ![v3041_pa,v3041_pb,v3041_pg]
  minus := ![(Primitive.Addresses.material3041 1).one,v3041_mb,v3041_mg]
  upper := v3041_upper
  lower := (Primitive.Addresses.material3041 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3041_pa_checked.trans (by decide +kernel)
    · exact v3041_pb_checked.trans (by decide +kernel)
    · exact v3041_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 38 97 Primitive.Addresses.material3041
    · exact v3041_mb_checked.trans (by decide +kernel)
    · exact v3041_mg_checked.trans (by decide +kernel)
  upper_error := v3041_upper_checked
  lower_error := reuse_lower_error 38 97 Primitive.Addresses.material3041

def v3042_pa : Scalar.QComplex := ((999999606395926392727714208918 : Int)/10^30,(-887247424504787058749653903 : Int)/10^30)
theorem v3042_pa_checked : Scalar.distance (sourceCoefficient 39 40 1 0) v3042_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3042_pb : Scalar.QComplex := ((-382827319206558497562100 : Int)/10^30,(-431477351132170755915349034 : Int)/10^30)
theorem v3042_pb_checked : Scalar.distance (sourceCoefficient 39 40 1 1) v3042_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3042_pg : Scalar.QComplex := ((-93086393253768326445774 : Int)/10^30,(82590695178879797056 : Int)/10^30)
theorem v3042_pg_checked : Scalar.distance (sourceCoefficient 39 40 1 2) v3042_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3042_mb : Scalar.QComplex := ((-755172697671007409647008 : Int)/10^30,(-431476860110698867446486471 : Int)/10^30)
theorem v3042_mb_checked : Scalar.distance (sourceCoefficient 39 40 3 1) v3042_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3042_mg : Scalar.QComplex := ((-93086287321399667185602 : Int)/10^30,(162920029349070581165 : Int)/10^30)
theorem v3042_mg_checked : Scalar.distance (sourceCoefficient 39 40 3 2) v3042_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3042_upper : Scalar.QComplex := ((999996585705416633785653043739 : Int)/10^30,(-2613154704437708312934564578 : Int)/10^30)
theorem v3042_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 40 5) 1) 14) v3042_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3042 : Material (39 : Basis) (40 : Basis) where
  plus := ![v3042_pa,v3042_pb,v3042_pg]
  minus := ![(Primitive.Addresses.material3042 1).one,v3042_mb,v3042_mg]
  upper := v3042_upper
  lower := (Primitive.Addresses.material3042 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3042_pa_checked.trans (by decide +kernel)
    · exact v3042_pb_checked.trans (by decide +kernel)
    · exact v3042_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 40 Primitive.Addresses.material3042
    · exact v3042_mb_checked.trans (by decide +kernel)
    · exact v3042_mg_checked.trans (by decide +kernel)
  upper_error := v3042_upper_checked
  lower_error := reuse_lower_error 39 40 Primitive.Addresses.material3042

def v3043_pa : Scalar.QComplex := ((999999593440146697728751432974 : Int)/10^30,(-901731413068008948782794884 : Int)/10^30)
theorem v3043_pa_checked : Scalar.distance (sourceCoefficient 39 41 1 0) v3043_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3043_pb : Scalar.QComplex := ((-389076834629169290748547 : Int)/10^30,(-431477345479594775869000036 : Int)/10^30)
theorem v3043_pb_checked : Scalar.distance (sourceCoefficient 39 41 1 1) v3043_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3043_pg : Scalar.QComplex := ((-93086392041024791174859 : Int)/10^30,(83938957958766380644 : Int)/10^30)
theorem v3043_pg_checked : Scalar.distance (sourceCoefficient 39 41 1 2) v3043_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3043_mb : Scalar.QComplex := ((-761422205888719505822471 : Int)/10^30,(-431476849065074650125457069 : Int)/10^30)
theorem v3043_mb_checked : Scalar.distance (sourceCoefficient 39 41 3 1) v3043_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3043_mg : Scalar.QComplex := ((-93086284945166527933852 : Int)/10^30,(164268290580394262151 : Int)/10^30)
theorem v3043_mg_checked : Scalar.distance (sourceCoefficient 39 41 3 2) v3043_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3043_upper : Scalar.QComplex := ((999996547751605951955900039208 : Int)/10^30,(-2627638649068230232447261875 : Int)/10^30)
theorem v3043_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 41 5) 1) 14) v3043_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3043 : Material (39 : Basis) (41 : Basis) where
  plus := ![v3043_pa,v3043_pb,v3043_pg]
  minus := ![(Primitive.Addresses.material3043 1).one,v3043_mb,v3043_mg]
  upper := v3043_upper
  lower := (Primitive.Addresses.material3043 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3043_pa_checked.trans (by decide +kernel)
    · exact v3043_pb_checked.trans (by decide +kernel)
    · exact v3043_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 41 Primitive.Addresses.material3043
    · exact v3043_mb_checked.trans (by decide +kernel)
    · exact v3043_mg_checked.trans (by decide +kernel)
  upper_error := v3043_upper_checked
  lower_error := reuse_lower_error 39 41 Primitive.Addresses.material3043

def v3044_pa : Scalar.QComplex := ((999999582836378713186780398623 : Int)/10^30,(-913415058200892325356581209 : Int)/10^30)
theorem v3044_pa_checked : Scalar.distance (sourceCoefficient 39 42 1 0) v3044_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3044_pb : Scalar.QComplex := ((-394118064800097866911000 : Int)/10^30,(-431477340831946580426154604 : Int)/10^30)
theorem v3044_pb_checked : Scalar.distance (sourceCoefficient 39 42 1 1) v3044_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3044_pg : Scalar.QComplex := ((-93086391046152384881458 : Int)/10^30,(85026546765114456917 : Int)/10^30)
theorem v3044_pg_checked : Scalar.distance (sourceCoefficient 39 42 1 2) v3044_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3044_mb : Scalar.QComplex := ((-766463430171856623384768 : Int)/10^30,(-431476840067073596281540796 : Int)/10^30)
theorem v3044_mb_checked : Scalar.distance (sourceCoefficient 39 42 3 1) v3044_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3044_mg : Scalar.QComplex := ((-93086283011754335380023 : Int)/10^30,(165355878123253241315 : Int)/10^30)
theorem v3044_mg_checked : Scalar.distance (sourceCoefficient 39 42 3 2) v3044_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3044_upper : Scalar.QComplex := ((999996516982942193130748649175 : Int)/10^30,(-2639322258498555065956086136 : Int)/10^30)
theorem v3044_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 42 5) 1) 14) v3044_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3044 : Material (39 : Basis) (42 : Basis) where
  plus := ![v3044_pa,v3044_pb,v3044_pg]
  minus := ![(Primitive.Addresses.material3044 1).one,v3044_mb,v3044_mg]
  upper := v3044_upper
  lower := (Primitive.Addresses.material3044 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3044_pa_checked.trans (by decide +kernel)
    · exact v3044_pb_checked.trans (by decide +kernel)
    · exact v3044_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 42 Primitive.Addresses.material3044
    · exact v3044_mb_checked.trans (by decide +kernel)
    · exact v3044_mg_checked.trans (by decide +kernel)
  upper_error := v3044_upper_checked
  lower_error := reuse_lower_error 39 42 Primitive.Addresses.material3044

def v3045_pa : Scalar.QComplex := ((999999568578952714824939261296 : Int)/10^30,(-928892840130781759940710047 : Int)/10^30)
theorem v3045_pa_checked : Scalar.distance (sourceCoefficient 39 43 1 0) v3045_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3045_pb : Scalar.QComplex := ((-400796379658008182117665 : Int)/10^30,(-431477334554096634834251033 : Int)/10^30)
theorem v3045_pb_checked : Scalar.distance (sourceCoefficient 39 43 1 1) v3045_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3045_pg : Scalar.QComplex := ((-93086389705378127699653 : Int)/10^30,(86467318214770434342 : Int)/10^30)
theorem v3045_pg_checked : Scalar.distance (sourceCoefficient 39 43 1 2) v3045_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3045_mb : Scalar.QComplex := ((-773141737125623343744327 : Int)/10^30,(-431476828026141045979198665 : Int)/10^30)
theorem v3045_mb_checked : Scalar.distance (sourceCoefficient 39 43 3 1) v3045_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3045_mg : Scalar.QComplex := ((-93086280427659706313906 : Int)/10^30,(166796647879416363808 : Int)/10^30)
theorem v3045_mg_checked : Scalar.distance (sourceCoefficient 39 43 3 2) v3045_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3045_upper : Scalar.QComplex := ((999996476012289951949164391615 : Int)/10^30,(-2654799992769082614363679910 : Int)/10^30)
theorem v3045_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 43 5) 1) 14) v3045_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3045 : Material (39 : Basis) (43 : Basis) where
  plus := ![v3045_pa,v3045_pb,v3045_pg]
  minus := ![(Primitive.Addresses.material3045 1).one,v3045_mb,v3045_mg]
  upper := v3045_upper
  lower := (Primitive.Addresses.material3045 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3045_pa_checked.trans (by decide +kernel)
    · exact v3045_pb_checked.trans (by decide +kernel)
    · exact v3045_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 43 Primitive.Addresses.material3045
    · exact v3045_mb_checked.trans (by decide +kernel)
    · exact v3045_mg_checked.trans (by decide +kernel)
  upper_error := v3045_upper_checked
  lower_error := reuse_lower_error 39 43 Primitive.Addresses.material3045

def v3046_pa : Scalar.QComplex := ((999999563122416064214517097683 : Int)/10^30,(-934748617013979657610527530 : Int)/10^30)
theorem v3046_pa_checked : Scalar.distance (sourceCoefficient 39 44 1 0) v3046_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3046_pb : Scalar.QComplex := ((-403323015696368562595416 : Int)/10^30,(-431477332143035429707375021 : Int)/10^30)
theorem v3046_pb_checked : Scalar.distance (sourceCoefficient 39 44 1 1) v3046_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3046_pg : Scalar.QComplex := ((-93086389191333679504793 : Int)/10^30,(87012411573196361676 : Int)/10^30)
theorem v3046_pg_checked : Scalar.distance (sourceCoefficient 39 44 1 2) v3046_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3046_mb : Scalar.QComplex := ((-775668370142564424310202 : Int)/10^30,(-431476823434707632958473516 : Int)/10^30)
theorem v3046_mb_checked : Scalar.distance (sourceCoefficient 39 44 3 1) v3046_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3046_mg : Scalar.QComplex := ((-93086279443224431293234 : Int)/10^30,(167341740591281914713 : Int)/10^30)
theorem v3046_mg_checked : Scalar.distance (sourceCoefficient 39 44 3 2) v3046_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3046_upper : Scalar.QComplex := ((999996460449221759738629728649 : Int)/10^30,(-2660655751513301466567536147 : Int)/10^30)
theorem v3046_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 44 5) 1) 14) v3046_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3046 : Material (39 : Basis) (44 : Basis) where
  plus := ![v3046_pa,v3046_pb,v3046_pg]
  minus := ![(Primitive.Addresses.material3046 1).one,v3046_mb,v3046_mg]
  upper := v3046_upper
  lower := (Primitive.Addresses.material3046 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3046_pa_checked.trans (by decide +kernel)
    · exact v3046_pb_checked.trans (by decide +kernel)
    · exact v3046_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 44 Primitive.Addresses.material3046
    · exact v3046_mb_checked.trans (by decide +kernel)
    · exact v3046_mg_checked.trans (by decide +kernel)
  upper_error := v3046_upper_checked
  lower_error := reuse_lower_error 39 44 Primitive.Addresses.material3046

def v3047_pa : Scalar.QComplex := ((999999560394947281258521180760 : Int)/10^30,(-937661939178977543397424381 : Int)/10^30)
theorem v3047_pa_checked : Scalar.distance (sourceCoefficient 39 45 1 0) v3047_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3047_pb : Scalar.QComplex := ((-404580048692796902924154 : Int)/10^30,(-431477330936153648925646527 : Int)/10^30)
theorem v3047_pb_checked : Scalar.distance (sourceCoefficient 39 45 1 1) v3047_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3047_pg : Scalar.QComplex := ((-93086388934202917916595 : Int)/10^30,(87283602329525828201 : Int)/10^30)
theorem v3047_pg_checked : Scalar.distance (sourceCoefficient 39 45 1 2) v3047_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3047_mb : Scalar.QComplex := ((-776925401629457309945670 : Int)/10^30,(-431476821143063440300855522 : Int)/10^30)
theorem v3047_mb_checked : Scalar.distance (sourceCoefficient 39 45 3 1) v3047_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3047_mg : Scalar.QComplex := ((-93086278952068356712501 : Int)/10^30,(167612931024742402116 : Int)/10^30)
theorem v3047_mg_checked : Scalar.distance (sourceCoefficient 39 45 3 2) v3047_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3047_upper : Scalar.QComplex := ((999996452693627276762897266855 : Int)/10^30,(-2663569064631884525104519815 : Int)/10^30)
theorem v3047_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 45 5) 1) 14) v3047_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3047 : Material (39 : Basis) (45 : Basis) where
  plus := ![v3047_pa,v3047_pb,v3047_pg]
  minus := ![(Primitive.Addresses.material3047 1).one,v3047_mb,v3047_mg]
  upper := v3047_upper
  lower := (Primitive.Addresses.material3047 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3047_pa_checked.trans (by decide +kernel)
    · exact v3047_pb_checked.trans (by decide +kernel)
    · exact v3047_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 45 Primitive.Addresses.material3047
    · exact v3047_mb_checked.trans (by decide +kernel)
    · exact v3047_mg_checked.trans (by decide +kernel)
  upper_error := v3047_upper_checked
  lower_error := reuse_lower_error 39 45 Primitive.Addresses.material3047

def v3048_pa : Scalar.QComplex := ((999999544916925065899847034038 : Int)/10^30,(-954026175095628712412929962 : Int)/10^30)
theorem v3048_pa_checked : Scalar.distance (sourceCoefficient 39 46 1 0) v3048_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3048_pb : Scalar.QComplex := ((-411640848450263440420536 : Int)/10^30,(-431477324066311637892844702 : Int)/10^30)
theorem v3048_pb_checked : Scalar.distance (sourceCoefficient 39 46 1 1) v3048_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3048_pg : Scalar.QComplex := ((-93086387472760368520007 : Int)/10^30,(88806890608620075955 : Int)/10^30)
theorem v3048_pg_checked : Scalar.distance (sourceCoefficient 39 46 1 2) v3048_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3048_mb : Scalar.QComplex := ((-783986192829501153924083 : Int)/10^30,(-431476808180071803146695642 : Int)/10^30)
theorem v3048_mb_checked : Scalar.distance (sourceCoefficient 39 46 3 1) v3048_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3048_mg : Scalar.QComplex := ((-93086276176097172976732 : Int)/10^30,(169136217475487706649 : Int)/10^30)
theorem v3048_mg_checked : Scalar.distance (sourceCoefficient 39 46 3 2) v3048_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3048_upper : Scalar.QComplex := ((999996408972441473845894637243 : Int)/10^30,(-2679933249462266385949203727 : Int)/10^30)
theorem v3048_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 46 5) 1) 14) v3048_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3048 : Material (39 : Basis) (46 : Basis) where
  plus := ![v3048_pa,v3048_pb,v3048_pg]
  minus := ![(Primitive.Addresses.material3048 1).one,v3048_mb,v3048_mg]
  upper := v3048_upper
  lower := (Primitive.Addresses.material3048 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3048_pa_checked.trans (by decide +kernel)
    · exact v3048_pb_checked.trans (by decide +kernel)
    · exact v3048_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 46 Primitive.Addresses.material3048
    · exact v3048_mb_checked.trans (by decide +kernel)
    · exact v3048_mg_checked.trans (by decide +kernel)
  upper_error := v3048_upper_checked
  lower_error := reuse_lower_error 39 46 Primitive.Addresses.material3048

def v3049_pa : Scalar.QComplex := ((999999541152175161472085512997 : Int)/10^30,(-957964215999600618654847391 : Int)/10^30)
theorem v3049_pa_checked : Scalar.distance (sourceCoefficient 39 47 1 0) v3049_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3049_pb : Scalar.QComplex := ((-413340024525201878796292 : Int)/10^30,(-431477322390091271109700304 : Int)/10^30)
theorem v3049_pb_checked : Scalar.distance (sourceCoefficient 39 47 1 1) v3049_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3049_pg : Scalar.QComplex := ((-93086387116723943998184 : Int)/10^30,(89173468771559955671 : Int)/10^30)
theorem v3049_pg_checked : Scalar.distance (sourceCoefficient 39 47 1 2) v3049_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3049_mb : Scalar.QComplex := ((-785685366825256001046333 : Int)/10^30,(-431476805037539635874689026 : Int)/10^30)
theorem v3049_mb_checked : Scalar.distance (sourceCoefficient 39 47 3 1) v3049_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3049_mg : Scalar.QComplex := ((-93086275503720436474001 : Int)/10^30,(169502795194690383776 : Int)/10^30)
theorem v3049_mg_checked : Scalar.distance (sourceCoefficient 39 47 3 2) v3049_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3049_upper : Scalar.QComplex := ((999996398410995832595442420781 : Int)/10^30,(-2683871278003372160906143125 : Int)/10^30)
theorem v3049_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 47 5) 1) 14) v3049_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3049 : Material (39 : Basis) (47 : Basis) where
  plus := ![v3049_pa,v3049_pb,v3049_pg]
  minus := ![(Primitive.Addresses.material3049 1).one,v3049_mb,v3049_mg]
  upper := v3049_upper
  lower := (Primitive.Addresses.material3049 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3049_pa_checked.trans (by decide +kernel)
    · exact v3049_pb_checked.trans (by decide +kernel)
    · exact v3049_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 47 Primitive.Addresses.material3049
    · exact v3049_mb_checked.trans (by decide +kernel)
    · exact v3049_mg_checked.trans (by decide +kernel)
  upper_error := v3049_upper_checked
  lower_error := reuse_lower_error 39 47 Primitive.Addresses.material3049

def v3050_pa : Scalar.QComplex := ((999999514498454912710793845158 : Int)/10^30,(-985394770872480391489874093 : Int)/10^30)
theorem v3050_pa_checked : Scalar.distance (sourceCoefficient 39 48 1 0) v3050_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3050_pb : Scalar.QComplex := ((-425175691907571774473010 : Int)/10^30,(-431477310466810095850810472 : Int)/10^30)
theorem v3050_pb_checked : Scalar.distance (sourceCoefficient 39 48 1 1) v3050_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3050_pg : Scalar.QComplex := ((-93086384590017102904518 : Int)/10^30,(91726881147970016060 : Int)/10^30)
theorem v3050_pg_checked : Scalar.distance (sourceCoefficient 39 48 1 2) v3050_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3050_mb : Scalar.QComplex := ((-797521019511411363946698 : Int)/10^30,(-431476782900615007883915576 : Int)/10^30)
theorem v3050_mb_checked : Scalar.distance (sourceCoefficient 39 48 3 1) v3050_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3050_mg : Scalar.QComplex := ((-93086270773534656771267 : Int)/10^30,(172056204439914114505 : Int)/10^30)
theorem v3050_mg_checked : Scalar.distance (sourceCoefficient 39 48 3 2) v3050_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3050_upper : Scalar.QComplex := ((999996324414666051328132222591 : Int)/10^30,(-2711301746019759527161225883 : Int)/10^30)
theorem v3050_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 48 5) 1) 14) v3050_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3050 : Material (39 : Basis) (48 : Basis) where
  plus := ![v3050_pa,v3050_pb,v3050_pg]
  minus := ![(Primitive.Addresses.material3050 1).one,v3050_mb,v3050_mg]
  upper := v3050_upper
  lower := (Primitive.Addresses.material3050 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3050_pa_checked.trans (by decide +kernel)
    · exact v3050_pb_checked.trans (by decide +kernel)
    · exact v3050_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 48 Primitive.Addresses.material3050
    · exact v3050_mb_checked.trans (by decide +kernel)
    · exact v3050_mg_checked.trans (by decide +kernel)
  upper_error := v3050_upper_checked
  lower_error := reuse_lower_error 39 48 Primitive.Addresses.material3050

def v3051_pa : Scalar.QComplex := ((999999492539101429573507922093 : Int)/10^30,(-1007433143997302386872394880 : Int)/10^30)
theorem v3051_pa_checked : Scalar.distance (sourceCoefficient 39 49 1 0) v3051_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3051_pb : Scalar.QComplex := ((-434684754066002269296098 : Int)/10^30,(-431477300573754336325495363 : Int)/10^30)
theorem v3051_pb_checked : Scalar.distance (sourceCoefficient 39 49 1 1) v3051_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3051_pg : Scalar.QComplex := ((-93086382500800350773243 : Int)/10^30,(93778354574964847916 : Int)/10^30)
theorem v3051_pg_checked : Scalar.distance (sourceCoefficient 39 49 1 2) v3051_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3051_mb : Scalar.QComplex := ((-807030069591921877797357 : Int)/10^30,(-431476764801670561531279754 : Int)/10^30)
theorem v3051_mb_checked : Scalar.distance (sourceCoefficient 39 49 3 1) v3051_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3051_mg : Scalar.QComplex := ((-93086266913989509987622 : Int)/10^30,(174107675300151670264 : Int)/10^30)
theorem v3051_mg_checked : Scalar.distance (sourceCoefficient 39 49 3 2) v3051_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3051_upper : Scalar.QComplex := ((999996264419112566217734180947 : Int)/10^30,(-2733340048421161587373865704 : Int)/10^30)
theorem v3051_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 49 5) 1) 14) v3051_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3051 : Material (39 : Basis) (49 : Basis) where
  plus := ![v3051_pa,v3051_pb,v3051_pg]
  minus := ![(Primitive.Addresses.material3051 1).one,v3051_mb,v3051_mg]
  upper := v3051_upper
  lower := (Primitive.Addresses.material3051 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3051_pa_checked.trans (by decide +kernel)
    · exact v3051_pb_checked.trans (by decide +kernel)
    · exact v3051_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 49 Primitive.Addresses.material3051
    · exact v3051_mb_checked.trans (by decide +kernel)
    · exact v3051_mg_checked.trans (by decide +kernel)
  upper_error := v3051_upper_checked
  lower_error := reuse_lower_error 39 49 Primitive.Addresses.material3051

def v3052_pa : Scalar.QComplex := ((999999489941361859405256878166 : Int)/10^30,(-1010008423787334134334047222 : Int)/10^30)
theorem v3052_pa_checked : Scalar.distance (sourceCoefficient 39 50 1 0) v3052_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3052_pb : Scalar.QComplex := ((-435795929347956935220078 : Int)/10^30,(-431477299399474313868015609 : Int)/10^30)
theorem v3052_pb_checked : Scalar.distance (sourceCoefficient 39 50 1 1) v3052_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3052_pg : Scalar.QComplex := ((-93086382253224335470137 : Int)/10^30,(94018078170377296102 : Int)/10^30)
theorem v3052_pg_checked : Scalar.distance (sourceCoefficient 39 50 1 2) v3052_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3052_mb : Scalar.QComplex := ((-808141243446784431258614 : Int)/10^30,(-431476762668496753461966726 : Int)/10^30)
theorem v3052_mb_checked : Scalar.distance (sourceCoefficient 39 50 3 1) v3052_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3052_mg : Scalar.QComplex := ((-93086266459542920777381 : Int)/10^30,(174347398592657117171 : Int)/10^30)
theorem v3052_mg_checked : Scalar.distance (sourceCoefficient 39 50 3 2) v3052_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3052_upper : Scalar.QComplex := ((999996257376677575040178211648 : Int)/10^30,(-2735915319892153768180279407 : Int)/10^30)
theorem v3052_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 50 5) 1) 14) v3052_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3052 : Material (39 : Basis) (50 : Basis) where
  plus := ![v3052_pa,v3052_pb,v3052_pg]
  minus := ![(Primitive.Addresses.material3052 1).one,v3052_mb,v3052_mg]
  upper := v3052_upper
  lower := (Primitive.Addresses.material3052 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3052_pa_checked.trans (by decide +kernel)
    · exact v3052_pb_checked.trans (by decide +kernel)
    · exact v3052_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 50 Primitive.Addresses.material3052
    · exact v3052_mb_checked.trans (by decide +kernel)
    · exact v3052_mg_checked.trans (by decide +kernel)
  upper_error := v3052_upper_checked
  lower_error := reuse_lower_error 39 50 Primitive.Addresses.material3052

def v3053_pa : Scalar.QComplex := ((999999478465187162326295106260 : Int)/10^30,(-1021307668470567398079451384 : Int)/10^30)
theorem v3053_pa_checked : Scalar.distance (sourceCoefficient 39 51 1 0) v3053_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3053_pb : Scalar.QComplex := ((-440671299164991764214484 : Int)/10^30,(-431477294202131735686653688 : Int)/10^30)
theorem v3053_pb_checked : Scalar.distance (sourceCoefficient 39 51 1 1) v3053_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3053_pg : Scalar.QComplex := ((-93086381158452121034104 : Int)/10^30,(95069884489555704161 : Int)/10^30)
theorem v3053_pg_checked : Scalar.distance (sourceCoefficient 39 51 1 2) v3053_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3053_mb : Scalar.QComplex := ((-813016606963423696612772 : Int)/10^30,(-431476753263931536893141510 : Int)/10^30)
theorem v3053_mb_checked : Scalar.distance (sourceCoefficient 39 51 3 1) v3053_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3053_mg : Scalar.QComplex := ((-93086264457109632122211 : Int)/10^30,(175399203575460848329 : Int)/10^30)
theorem v3053_mg_checked : Scalar.distance (sourceCoefficient 39 51 3 2) v3053_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3053_upper : Scalar.QComplex := ((999996226399048706585066105011 : Int)/10^30,(-2747214527939652962045668954 : Int)/10^30)
theorem v3053_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 51 5) 1) 14) v3053_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3053 : Material (39 : Basis) (51 : Basis) where
  plus := ![v3053_pa,v3053_pb,v3053_pg]
  minus := ![(Primitive.Addresses.material3053 1).one,v3053_mb,v3053_mg]
  upper := v3053_upper
  lower := (Primitive.Addresses.material3053 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3053_pa_checked.trans (by decide +kernel)
    · exact v3053_pb_checked.trans (by decide +kernel)
    · exact v3053_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 51 Primitive.Addresses.material3053
    · exact v3053_mb_checked.trans (by decide +kernel)
    · exact v3053_mg_checked.trans (by decide +kernel)
  upper_error := v3053_upper_checked
  lower_error := reuse_lower_error 39 51 Primitive.Addresses.material3053

def v3054_pa : Scalar.QComplex := ((999999453468293240715401835745 : Int)/10^30,(-1045496587666197360655774953 : Int)/10^30)
theorem v3054_pa_checked : Scalar.distance (sourceCoefficient 39 52 1 0) v3054_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3054_pb : Scalar.QComplex := ((-451108273398141408487855 : Int)/10^30,(-431477282828966124558058992 : Int)/10^30)
theorem v3054_pb_checked : Scalar.distance (sourceCoefficient 39 52 1 1) v3054_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3054_pg : Scalar.QComplex := ((-93086378768199931670542 : Int)/10^30,(97321544549666039722 : Int)/10^30)
theorem v3054_pg_checked : Scalar.distance (sourceCoefficient 39 52 1 2) v3054_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3054_mb : Scalar.QComplex := ((-823453567495881146558466 : Int)/10^30,(-431476732884131461175610160 : Int)/10^30)
theorem v3054_mb_checked : Scalar.distance (sourceCoefficient 39 52 3 1) v3054_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3054_mg : Scalar.QComplex := ((-93086260123777111888113 : Int)/10^30,(177650860734495251104 : Int)/10^30)
theorem v3054_mg_checked : Scalar.distance (sourceCoefficient 39 52 3 2) v3054_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3054_upper : Scalar.QComplex := ((999996159654311884861715141520 : Int)/10^30,(-2771403367966358004581318960 : Int)/10^30)
theorem v3054_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 52 5) 1) 14) v3054_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3054 : Material (39 : Basis) (52 : Basis) where
  plus := ![v3054_pa,v3054_pb,v3054_pg]
  minus := ![(Primitive.Addresses.material3054 1).one,v3054_mb,v3054_mg]
  upper := v3054_upper
  lower := (Primitive.Addresses.material3054 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3054_pa_checked.trans (by decide +kernel)
    · exact v3054_pb_checked.trans (by decide +kernel)
    · exact v3054_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 52 Primitive.Addresses.material3054
    · exact v3054_mb_checked.trans (by decide +kernel)
    · exact v3054_mg_checked.trans (by decide +kernel)
  upper_error := v3054_upper_checked
  lower_error := reuse_lower_error 39 52 Primitive.Addresses.material3054

def v3055_pa : Scalar.QComplex := ((999999449590288655915257767773 : Int)/10^30,(-1049199275513150143628550394 : Int)/10^30)
theorem v3055_pa_checked : Scalar.distance (sourceCoefficient 39 53 1 0) v3055_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3055_pb : Scalar.QComplex := ((-452705899860503587624697 : Int)/10^30,(-431477281058326401238932566 : Int)/10^30)
theorem v3055_pb_checked : Scalar.distance (sourceCoefficient 39 53 1 1) v3055_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3055_pg : Scalar.QComplex := ((-93086378396707312304624 : Int)/10^30,(97666214530401210649 : Int)/10^30)
theorem v3055_pg_checked : Scalar.distance (sourceCoefficient 39 53 1 2) v3055_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3055_mb : Scalar.QComplex := ((-825051191835391644049915 : Int)/10^30,(-431476729734812714552805353 : Int)/10^30)
theorem v3055_mb_checked : Scalar.distance (sourceCoefficient 39 53 3 1) v3055_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3055_mg : Scalar.QComplex := ((-93086259454849960831101 : Int)/10^30,(177995530266312636900 : Int)/10^30)
theorem v3055_mg_checked : Scalar.distance (sourceCoefficient 39 53 3 2) v3055_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3055_upper : Scalar.QComplex := ((999996149385809757270882298876 : Int)/10^30,(-2775106043605508084248573480 : Int)/10^30)
theorem v3055_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 53 5) 1) 14) v3055_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3055 : Material (39 : Basis) (53 : Basis) where
  plus := ![v3055_pa,v3055_pb,v3055_pg]
  minus := ![(Primitive.Addresses.material3055 1).one,v3055_mb,v3055_mg]
  upper := v3055_upper
  lower := (Primitive.Addresses.material3055 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3055_pa_checked.trans (by decide +kernel)
    · exact v3055_pb_checked.trans (by decide +kernel)
    · exact v3055_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 53 Primitive.Addresses.material3055
    · exact v3055_mb_checked.trans (by decide +kernel)
    · exact v3055_mg_checked.trans (by decide +kernel)
  upper_error := v3055_upper_checked
  lower_error := reuse_lower_error 39 53 Primitive.Addresses.material3055

def v3056_pa : Scalar.QComplex := ((999999447613430648293647015960 : Int)/10^30,(-1051081744476846437165977979 : Int)/10^30)
theorem v3056_pa_checked : Scalar.distance (sourceCoefficient 39 54 1 0) v3056_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3056_pb : Scalar.QComplex := ((-453518142844876553049337 : Int)/10^30,(-431477280155098083837370516 : Int)/10^30)
theorem v3056_pb_checked : Scalar.distance (sourceCoefficient 39 54 1 1) v3056_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3056_pg : Scalar.QComplex := ((-93086378207267301820249 : Int)/10^30,(97841446839427176907 : Int)/10^30)
theorem v3056_pg_checked : Scalar.distance (sourceCoefficient 39 54 1 2) v3056_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3056_mb : Scalar.QComplex := ((-825863433737884067030042 : Int)/10^30,(-431476728130655620016582318 : Int)/10^30)
theorem v3056_mb_checked : Scalar.distance (sourceCoefficient 39 54 3 1) v3056_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3056_mg : Scalar.QComplex := ((-93086259114192430364718 : Int)/10^30,(178170762346613409009 : Int)/10^30)
theorem v3056_mg_checked : Scalar.distance (sourceCoefficient 39 54 3 2) v3056_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3056_upper : Scalar.QComplex := ((999996144159984038857608869286 : Int)/10^30,(-2776988506353610404701037287 : Int)/10^30)
theorem v3056_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 39 54 5) 1) 14) v3056_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3056 : Material (39 : Basis) (54 : Basis) where
  plus := ![v3056_pa,v3056_pb,v3056_pg]
  minus := ![(Primitive.Addresses.material3056 1).one,v3056_mb,v3056_mg]
  upper := v3056_upper
  lower := (Primitive.Addresses.material3056 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3056_pa_checked.trans (by decide +kernel)
    · exact v3056_pb_checked.trans (by decide +kernel)
    · exact v3056_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 39 54 Primitive.Addresses.material3056
    · exact v3056_mb_checked.trans (by decide +kernel)
    · exact v3056_mg_checked.trans (by decide +kernel)
  upper_error := v3056_upper_checked
  lower_error := reuse_lower_error 39 54 Primitive.Addresses.material3056

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
