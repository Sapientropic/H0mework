import H0mework.Versions.R2.Physics.SpinPair.CoframeMatter
import H0mework.Versions.R2.Physics.Homogeneous.GaugeBalance
import Mathlib.LinearAlgebra.Matrix.StdBasis

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineHolonomicField
open StageNineDiracDualFormNativeCoframeLocalVariation

noncomputable section

theorem actual_coframeEuler_coordinates
    (point : BasePoint) (row column : LorentzianIndex) :
    diracDualFormNativeCoframeEulerCovector positiveSmoothUnifiedSource point
      (toContinuumPointField actual point) (Matrix.single row column 1) = 0 := by
  rw [diracDualFormNativeCoframeEulerCovector_apply_eq_gauge_add_matter_sub_reaction
    positiveSmoothUnifiedSource point (toContinuumPointField actual point) (actual_nondegenerate point),
    actual_gaugeCoframe_coordinates, actual_matterCoframe_coordinates,
    actual_gravityReaction_coordinates]
  by_cases diagonal : row = column
  · subst column
    by_cases temporal : row = 0
    · simp only [if_pos temporal, if_true]
      have balance := coframe_time_balance
      rw [spinScale_sq] at balance
      linarith [balance]
    · simp only [if_neg temporal, if_true]
      have balance := coframe_spatial_balance
      rw [spinScale_sq] at balance
      linear_combination balance
  · simp [diagonal]

theorem actual_coframeEuler_zero (point : BasePoint) :
    diracDualFormNativeCoframeEulerCovector positiveSmoothUnifiedSource point
      (toContinuumPointField actual point) = 0 := by
  have linear : (diracDualFormNativeCoframeEulerCovector positiveSmoothUnifiedSource point
      (toContinuumPointField actual point)).toLinearMap = 0 := by
    apply (Matrix.stdBasis ℝ (Fin 4) (Fin 4)).ext
    intro index
    rcases index with ⟨row, column⟩
    rw [Matrix.stdBasis_eq_single]
    change diracDualFormNativeCoframeEulerCovector positiveSmoothUnifiedSource point
      (toContinuumPointField actual point) (Matrix.single row column 1) = 0
    exact actual_coframeEuler_coordinates point row column
  apply ContinuousLinearMap.ext
  intro coframe
  exact congrArg (fun map : LorentzianCoframe →ₗ[ℝ] ℝ => map coframe) linear

end
end SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
