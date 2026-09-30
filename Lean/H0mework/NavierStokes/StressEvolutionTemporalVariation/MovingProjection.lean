import H0mework.NavierStokes.VelocityGalerkin.InitialConvergence
import H0mework.NavierStokes.StressResolvent.ResolventCompactness

set_option autoImplicit false
open Filter
open scoped Topology

namespace SaturationMonoid.NavierStokes.NativeGalerkinMovingProjection

open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinInitialConvergence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open NativeResolventCompactness

noncomputable section

theorem projection_sub (radius : ℕ) (left right : State) :
    wholeRestartVelocityEndpointGalerkinInitialVelocity radius (left - right) =
      wholeRestartVelocityEndpointGalerkinInitialVelocity radius left -
        wholeRestartVelocityEndpointGalerkinInitialVelocity radius right := by
  apply lp.ext
  funext wave
  simp only [wholeRestartVelocityEndpointGalerkinInitialVelocity_apply, lp.coeFn_sub, Pi.sub_apply]
  split_ifs <;> simp

theorem projection_norm_le (radius : ℕ) (value : State) :
    ‖wholeRestartVelocityEndpointGalerkinInitialVelocity radius value‖ ≤ ‖value‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [wholeRestartVelocityEndpointGalerkinInitialVelocity_norm_sq]
  exact wholeRestartVelocityEndpointFiniteProjectedSquare_le_norm_sq radius value

/-- The original projection acts on every complete State, including weighted
action encodings, with the same cofinal radius and strong-input filter. -/
theorem moving_input {I : Type*} (f : Filter I) (radius : I → ℕ) (input : I → State) (target : State)
    (cofinal : Tendsto radius f atTop) (strong : Tendsto input f (𝓝 target)) :
    Tendsto (fun i => wholeRestartVelocityEndpointGalerkinInitialVelocity (radius i) (input i)) f
      (𝓝 target) := by
  have fixed := (wholeRestartVelocityEndpointGalerkinInitialVelocity_tendsto target).comp cofinal
  have error : Tendsto
      (fun i => wholeRestartVelocityEndpointGalerkinInitialVelocity (radius i) (input i - target)) f (𝓝 0) := by
    apply squeeze_zero_norm (fun i => projection_norm_le (radius i) (input i - target))
    simpa only [sub_self, norm_zero] using (strong.sub_const target).norm
  simpa only [projection_sub, Function.comp_apply, sub_add_cancel, zero_add] using error.add fixed

end
end SaturationMonoid.NavierStokes.NativeGalerkinMovingProjection
