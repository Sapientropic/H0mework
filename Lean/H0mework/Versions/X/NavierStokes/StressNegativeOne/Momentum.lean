import H0mework.Versions.X.NavierStokes.StressNegativeOne.Inclusion

set_option autoImplicit false
open scoped Topology

namespace SaturationMonoid.NavierStokes.NativeNegativeOneMomentum

open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open NativeResolventCompactness NativeWholeResolvent NativeWholeH1Mixed NativeWholeH1Pairing
open NativeNegativeOneInclusion NativeEndpointVelocityCarrier NativeWholeResolventZeroAction
open NativeCompleteStressBilinear NativeCompleteStressAction

noncomputable section

def momentum (nu : Viscosity) (value : wholePhysical) (regular : H1 value) : State :=
  negativeAction value value regular regular - nu.coeff • gradientValue value regular

def coefficient (nu : Viscosity) : ℝ := Real.sqrt NativeMovingCriticalProductWeights.constant + nu.coeff * (2 * Real.pi)

theorem coefficient_nonnegative (nu : Viscosity) : 0 ≤ coefficient nu := by
  have viscosity := nu.coeff_pos.le
  unfold coefficient
  positivity

theorem momentum_bound (nu : Viscosity) (value : wholePhysical) (regular : H1 value) :
    ‖momentum nu value regular‖ ≤ coefficient nu * (1 + gradientMass value) := by
  have gradientNonnegative : 0 ≤ gradientMass value := tsum_nonneg (gradient_nonnegative value)
  have nonlinear : ‖negativeAction value value regular regular‖ ≤
      Real.sqrt NativeMovingCriticalProductWeights.constant * gradientMass value := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) gradientNonnegative)).mp
    rw [mul_pow, Real.sq_sqrt NativeMovingCriticalProductWeights.constant_nonnegative]
    exact (negativeAction_bound value value regular regular).trans_eq (by ring)
  have viscous : ‖gradientValue value regular‖ ≤ (2 * Real.pi) * (1 + gradientMass value) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [gradientValue_norm_sq]
    calc
      _ ≤ (2 * Real.pi) ^ 2 * (1 + gradientMass value) ^ 2 :=
        mul_le_mul_of_nonneg_left (by nlinarith : gradientMass value ≤ (1 + gradientMass value) ^ 2) (sq_nonneg _)
      _ = _ := by ring
  have viscousRate : ‖nu.coeff • gradientValue value regular‖ ≤ nu.coeff * ((2 * Real.pi) * (1 + gradientMass value)) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos nu.coeff_pos]
    exact mul_le_mul_of_nonneg_left viscous nu.coeff_pos.le
  have rate := (norm_sub_le (negativeAction value value regular regular) (nu.coeff • gradientValue value regular)).trans
    (add_le_add nonlinear viscousRate)
  change ‖momentum nu value regular‖ ≤ _ at rate
  refine rate.trans ?_
  unfold coefficient
  nlinarith [Real.sqrt_nonneg NativeMovingCriticalProductWeights.constant]

theorem original_row (nu : Viscosity) (value : wholePhysical) (regular : H1 value) (wave : Wave) :
    momentum nu value regular wave = (lowerWeight wave)⁻¹ • (momentumOperator nu value.1 value.1 wave) := by
  have original := congrArg (fun state : State => state wave) (lower_momentum nu value regular)
  change lowerWeight wave • (momentum nu value regular wave) = momentumOperator nu value.1 value.1 wave at original
  have decoded := congrArg (fun vector : ComplexCoordinateEuclidean => (lowerWeight wave)⁻¹ • vector) original
  simpa only [inv_smul_smul₀ (lowerWeight_positive wave).ne'] using decoded

theorem original_continuous (nu : Viscosity) : Continuous (fun value : State => momentumOperator nu value value) := by
  have tensor := (mixedCLM.continuous.comp wholeVelocityCLM.continuous).clm_apply wholeVelocityCLM.continuous
  exact (divergenceCLM.continuous.comp tensor).sub (viscousCLM nu).continuous

end
end SaturationMonoid.NavierStokes.NativeNegativeOneMomentum
