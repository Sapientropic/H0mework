import H0mework.Physics.SourceCoframe.Matter
import H0mework.Physics.SourceCoframe.Gauge
import Mathlib.LinearAlgebra.Matrix.StdBasis

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceFamily.Coframe

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineHolonomicField
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeJointResidualCarrier
open Stage9C.Material.SpinPair

noncomputable section

theorem euler_coordinates (step : ℕ) (point : BasePoint) (row column : LorentzianIndex) :
    diracDualFormNativeCoframeEulerCovector (sourceAt step) point
      (toContinuumPointField (fieldAt step) point) (Matrix.single row column 1) = 0 := by
  rw [diracDualFormNativeCoframeEulerCovector_apply_eq_gauge_add_matter_sub_reaction
    (sourceAt step) point (toContinuumPointField (fieldAt step) point) (field_nondegenerate step point),
    gauge_coordinates, matter_coordinates, gravity_reaction_coordinates]
  by_cases diagonal : row = column
  · subst column
    by_cases temporal : row = 0
    · simp only [if_pos temporal, if_true]
      linear_combination coframe_time_balance_at step
    · simp only [if_neg temporal, if_true]
      linear_combination coframe_spatial_balance_at step
  · simp [diagonal]

theorem euler_zero (step : ℕ) (point : BasePoint) :
    diracDualFormNativeCoframeEulerCovector (sourceAt step) point
      (toContinuumPointField (fieldAt step) point) = 0 := by
  have linear : (diracDualFormNativeCoframeEulerCovector (sourceAt step) point
      (toContinuumPointField (fieldAt step) point)).toLinearMap = 0 := by
    apply (Matrix.stdBasis ℝ (Fin 4) (Fin 4)).ext
    intro index
    rcases index with ⟨row, column⟩
    rw [Matrix.stdBasis_eq_single]
    change diracDualFormNativeCoframeEulerCovector (sourceAt step) point
      (toContinuumPointField (fieldAt step) point) (Matrix.single row column 1) = 0
    exact euler_coordinates step point row column
  apply ContinuousLinearMap.ext
  intro coframe
  exact congrArg (fun map : LorentzianCoframe →ₗ[ℝ] ℝ => map coframe) linear

theorem residual_zero (step : ℕ) (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual (sourceAt step) (fieldAt step) point).coframe = 0 :=
  euler_zero step point

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceFamily.Coframe
