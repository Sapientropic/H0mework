import H0mework.Versions.X.NavierStokes.HigherTreeSextic.ShiftCriticalSum
import H0mework.Versions.X.NavierStokes.HigherTreeSextic.QuarterSchur
import H0mework.Versions.X.NavierStokes.HigherTreeSexticUniform.Schur

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSexticUniformSum
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open NativeUnheatedSexticLatticePower
noncomputable section

theorem critical_summable (wave : IntegerWavevector) (left middle right : NativeUnheatedSchur.Space IntegerWavevector) :
    Summable (NativeUnheatedSexticShiftCriticalSum.term wave left middle right) :=
  NativeUnheatedSchurThree.summable (NativeUnheatedSexticShiftCriticalSum.profile wave)
    (NativeUnheatedSexticShiftSchur.kernel wave) 16
    (NativeUnheatedSexticShiftCriticalSum.profile_nonnegative wave) (NativeUnheatedSexticShiftSchur.kernel_nonnegative wave)
    (by norm_num) (NativeUnheatedSexticShiftCriticalSum.square_sum wave) (density 3) 34560
    (density_positive 3) (by norm_num) (NativeUnheatedSexticUniformSchur.row_bound wave)
    (NativeUnheatedSexticUniformSchur.column_bound wave) left middle right

theorem critical_bound (wave : IntegerWavevector) (left middle right : NativeUnheatedSchur.Space IntegerWavevector) :
    (∑' index, NativeUnheatedSexticShiftCriticalSum.term wave left middle right index) ≤
      (16*34560)*‖left‖*‖middle‖*‖right‖ :=
  NativeUnheatedSchurThree.bound (NativeUnheatedSexticShiftCriticalSum.profile wave)
    (NativeUnheatedSexticShiftSchur.kernel wave) 16
    (NativeUnheatedSexticShiftCriticalSum.profile_nonnegative wave) (NativeUnheatedSexticShiftSchur.kernel_nonnegative wave)
    (by norm_num) (NativeUnheatedSexticShiftCriticalSum.square_sum wave) (density 3) 34560
    (density_positive 3) (by norm_num) (NativeUnheatedSexticUniformSchur.row_bound wave)
    (NativeUnheatedSexticUniformSchur.column_bound wave) left middle right

theorem quarter_row (wave first : IntegerWavevector) (observed : Finset IntegerWavevector) :
    (∑ last ∈ observed, NativeUnheatedSexticQuarterSchur.kernel wave first last*density 3 last) ≤
      17536*density 3 first := by
  have point (last : IntegerWavevector) : 2*(NativeUnheatedSexticQuarterSchur.kernel wave first last*density 3 last) ≤
      NativeUnheatedSexticShiftSchur.kernel wave first last*density 3 last+
        NativeUnheatedSexticHardy.kernel first last*density 3 last := by
    have paid := mul_le_mul_of_nonneg_right (NativeUnheatedSexticQuarterSchur.point_bound wave first last) (density_positive 3 last).le
    nlinarith only [paid]
  have compared := Finset.sum_le_sum (s := observed) (fun last _ => point last)
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at compared
  have paid := add_le_add (NativeUnheatedSexticUniformSchur.row_bound wave first observed)
    (NativeUnheatedSexticHardy.row_bound first observed)
  linarith

theorem quarter_column (wave last : IntegerWavevector) (observed : Finset IntegerWavevector) :
    (∑ first ∈ observed, NativeUnheatedSexticQuarterSchur.kernel wave first last*density 3 first) ≤
      17536*density 3 last := by
  simpa only [NativeUnheatedSexticQuarterSchur.kernel_symmetric wave] using quarter_row wave last observed

theorem quarter_summable (wave : IntegerWavevector) (left right : NativeUnheatedSchur.Space IntegerWavevector) :
    Summable (NativeUnheatedSchur.term (NativeUnheatedSexticQuarterSchur.kernel wave) left right) :=
  NativeUnheatedSchur.summable (NativeUnheatedSexticQuarterSchur.kernel wave) (density 3) 17536
    (NativeUnheatedSexticQuarterSchur.kernel_nonnegative wave) (density_positive 3) (by norm_num)
    (quarter_row wave) (quarter_column wave) left right

theorem quarter_bound (wave : IntegerWavevector) (left right : NativeUnheatedSchur.Space IntegerWavevector) :
    (∑' index, NativeUnheatedSchur.term (NativeUnheatedSexticQuarterSchur.kernel wave) left right index) ≤
      17536*‖left‖*‖right‖ :=
  NativeUnheatedSchur.bound (NativeUnheatedSexticQuarterSchur.kernel wave) (density 3) 17536
    (NativeUnheatedSexticQuarterSchur.kernel_nonnegative wave) (density_positive 3) (by norm_num)
    (quarter_row wave) (quarter_column wave) left right

end
end SaturationMonoid.NavierStokes.NativeUnheatedSexticUniformSum
