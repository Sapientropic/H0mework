import H0mework.NavierStokes.UnifiedAction.UnifiedRootActionFeed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

set_option autoImplicit false
open scoped Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeUnifiedSourceDerivative

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open PhysicsCore.ProofFreeRicherAnholonomicSource PhysicsCore.StageNineCanonicalCauchyState
open PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open NativeUnifiedRootActionFeed

noncomputable section

variable {nu : Viscosity}

/-- The shared primitive consumes the original complete Hilbert action
without a pointwise continuity input. -/
theorem primitive_hasDerivAt_ae (initial : GeneratedWholeRestartCurrent nu) (space : StageNineSpatialPoint) :
    ∀ᵐ time : ℝ, time ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (fun actual => generatedState initial (canonicalCauchySlicePoint actual space))
        (action initial time) time := by
  filter_upwards [(action_intervalIntegrable initial).ae_hasDerivAt_integral] with time derivative
  intro inside
  have actual := derivative (by simpa only [uIcc_of_le zero_le_one] using inside)
    0 (by simp)
  simpa [generatedState, canonicalTimePrimitive, profile, add_comm] using actual.const_add (state initial 0)

/-- Ordinary strong differentiation in the complete H⁻⁴ Hilbert carrier,
then literal readback to the original whole receipt. -/
theorem source_hasDerivAt_ae (initial : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, time ∈ Ioo (0 : ℝ) 1 → HasDerivAt (state initial) (action initial time) time := by
  filter_upwards [primitive_hasDerivAt_ae initial 0] with time derivative
  intro inside
  apply (derivative ⟨inside.1.le, inside.2.le⟩).congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds inside.1 inside.2] with actual member
  exact (generatedState_original initial ⟨actual, member⟩ 0).symm

theorem source_test_hasDerivAt_ae (initial : GeneratedWholeRestartCurrent nu)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (test : WholeRestartVelocityEndpointState →L[ℝ] E) :
    ∀ᵐ time : ℝ, time ∈ Ioo (0 : ℝ) 1 →
      HasDerivAt (fun actual => test (state initial actual)) (test (action initial time)) time := by
  filter_upwards [source_hasDerivAt_ae initial] with time derivative
  intro inside
  exact test.hasFDerivAt.comp_hasDerivAt time (derivative inside)

theorem global_hasDerivAt_ae (initial : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 < time →
      HasDerivAt (NativeGlobalHilbertAction.sourceState initial)
        (NativeGlobalHilbertAction.sourceAction initial time) time := by
  have each (horizon : ℕ) : ∀ᵐ time : ℝ, time ∈ Ioo (0 : ℝ) horizon →
      HasDerivAt (NativeGlobalHilbertAction.sourceState initial)
        (NativeGlobalHilbertAction.sourceAction initial time) time := by
    filter_upwards [(NativeGlobalHilbertAction.sourceAction_intervalIntegrable initial horizon
      (Nat.cast_nonneg horizon)).ae_hasDerivAt_integral] with time derivative
    intro inside
    have actual := derivative
      (by simpa only [uIcc_of_le (Nat.cast_nonneg horizon)] using ⟨inside.1.le, inside.2.le⟩)
      0 (by simp)
    apply (actual.const_add (NativeGlobalHilbertAction.sourceState initial 0)).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds inside.1] with sample positive
    exact eq_add_of_sub_eq
      (NativeGlobalHilbertAction.source_integral_write initial 0 sample le_rfl positive.le) |>.trans (add_comm _ _)
  filter_upwards [ae_all_iff.mpr each] with time all
  intro positive
  obtain ⟨horizon, above⟩ := exists_nat_gt time
  exact all horizon ⟨positive, above⟩

end
end SaturationMonoid.NavierStokes.NativeUnifiedSourceDerivative
