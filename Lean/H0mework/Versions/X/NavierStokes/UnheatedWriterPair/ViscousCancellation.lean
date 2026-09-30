import H0mework.Versions.X.NavierStokes.UnheatedWriterPair.NegativeKernel

set_option autoImplicit false
open scoped BigOperators Topology

namespace SaturationMonoid.NavierStokes.NativeUnheatedPairNegativeKernel

open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open NativeUnheatedStressPairEvolution NativeUnheatedPairInverseFlux
open NativeResolventCompactness NativeWholeResolvent NativeWholeH1Mixed NativeWholeH1Pairing NativeEndpointVelocityCarrier

noncomputable section
variable {nu : Viscosity}

theorem gradient_row (value : wholePhysical) (regular : H1 value) (wave : IntegerWavevector) :
    wholeVelocity (gradientValue value regular) wave = root wave • wholeVelocity value.1 wave := by
  by_cases zero : wave = 0
  · subst wave
    simp [wholeVelocity_zero]
  · funext coordinate
    simp only [Pi.smul_apply, wholeVelocity_nonzero _ ⟨wave,zero⟩, gradientValue]
    rfl

theorem kernel_gradient_cancel (order : ℕ) (first last : IntegerWavevector)
    (firstNonzero : first ≠ 0) (lastNonzero : last ≠ 0) :
    nu.coeff * gradedKernel nu order first last *
      (root first*(root last)⁻¹ + (root first)⁻¹*root last) = ((decay nu first last)⁻¹)^order := by
  have base : nu.coeff * kernel nu first last *
      (root first*(root last)⁻¹ + (root first)⁻¹*root last) = 1 := by
    unfold kernel
    field_simp [(root_positive first firstNonzero).ne', (root_positive last lastNonzero).ne',
      (decay_positive (nu := nu) first last (Or.inl firstNonzero)).ne']
    rw [root_sq, root_sq, decay]
  unfold gradedKernel
  calc
    _ = (nu.coeff * kernel nu first last * (root first*(root last)⁻¹ + (root first)⁻¹*root last)) *
        ((decay nu first last)⁻¹)^order := by ring
    _ = _ := by rw [base, one_mul]

theorem viscous_pair (order : ℕ) (value : wholePhysical) (regular : H1 value)
    (wave : IntegerWavevector) (output input : Coordinate) :
    nu.coeff • (bilinear nu order wave output input (gradientValue value regular) (inverseGradient value.1) +
      bilinear nu order wave output input (inverseGradient value.1) (gradientValue value regular)) =
      coefficient nu order (wholeVelocity value.1) (wholeVelocity value.1) wave output input := by
  have summable (left right : State) := NativeUnheatedPairKernelBilinear.summable_pair
    (gradedKernel nu order) wave output input ((2*nu.coeff)⁻¹ * rowBudget nu order wave)
    (graded_bound order wave) (wholeVelocity left) (wholeVelocity right)
  rw [bilinear_apply, bilinear_apply, ← neg_add,
    ← (summable (gradientValue value regular) (inverseGradient value.1)).tsum_add
      (summable (inverseGradient value.1) (gradientValue value regular)), smul_neg,
    ← Summable.tsum_const_smul nu.coeff
      ((summable (gradientValue value regular) (inverseGradient value.1)).add
        (summable (inverseGradient value.1) (gradientValue value regular))), coefficient]
  congr 1
  apply tsum_congr
  intro first
  by_cases leftZero : first = 0
  · subst first
    simp [wholeVelocity_zero]
  by_cases rightZero : wave-first = 0
  · simp [rightZero, wholeVelocity_zero]
  rw [gradient_row, gradient_row, inverse_row, inverse_row]
  have cancelled := congrArg (fun x : ℝ => (x : ℂ)) (kernel_gradient_cancel (nu := nu) order first (wave-first) leftZero rightZero)
  simp only [Pi.smul_apply, Complex.real_smul]
  push_cast at cancelled ⊢
  linear_combination (wholeVelocity value.1 first input * wholeVelocity value.1 (wave-first) output) * cancelled

end
end SaturationMonoid.NavierStokes.NativeUnheatedPairNegativeKernel
