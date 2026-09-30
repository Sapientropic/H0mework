import H0mework.Versions.X.Fock.PrimeFieldJoint.BornSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedBornDecoder

open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedAcquisitionJoint
open SourceGeneratedActionWords.Fock.OriginalHilbert SourceGeneratedJointTime SourceGeneratedJointClockGraph
open SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem prior_loss (runtime : LivingRuntimeState process) (depth : Nat)
    (proposal : SourceJointFiniteDecoder.Space (inventoryBound runtime)) :
    (historyPMF (inventoryBound (next runtime)) (Fin.last (inventoryBound (next runtime)))).toReal ≤
      ‖target runtime depth - SourceJointFiniteDecoder.action (inventoryBound runtime) proposal‖ ^ 2 := by
  have bound := coordinate_norm_le (inventoryBound (next runtime) + 1)
    (target runtime depth - SourceJointFiniteDecoder.action (inventoryBound runtime) proposal)
  rw [map_sub, target_coordinate, prior_coordinate, sub_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)] at bound
  have paid := Real.sq_sqrt (show 0 ≤ (historyPMF (inventoryBound (next runtime))
    (Fin.last (inventoryBound (next runtime)))).toReal from ENNReal.toReal_nonneg)
  nlinarith only [bound, paid, Real.sqrt_nonneg ((historyPMF (inventoryBound (next runtime))
    (Fin.last (inventoryBound (next runtime)))).toReal),
    norm_nonneg (target runtime depth - SourceJointFiniteDecoder.action (inventoryBound runtime) proposal)]

theorem prior_residual_lower (runtime : LivingRuntimeState process) (depth : Nat) :
    (historyPMF (inventoryBound (next runtime)) (Fin.last (inventoryBound (next runtime)))).toReal ≤
      ‖SourceJointFiniteDecoder.residual (inventoryBound runtime) (target runtime depth)‖ ^ 2 := by
  have source := prior_loss runtime depth (SourceJointFiniteDecoder.decode (inventoryBound runtime) (target runtime depth))
  rw [SourceJointFiniteDecoder.source_minimum_cost] at source
  exact source

theorem prior_residual_ne_zero (runtime : LivingRuntimeState process) (depth : Nat) :
    SourceJointFiniteDecoder.residual (inventoryBound runtime) (target runtime depth) ≠ 0 := by
  intro vanished
  have lower := prior_residual_lower runtime depth
  rw [vanished, norm_zero, zero_pow (by decide : 2 ≠ 0)] at lower
  have positive := SourceGeneratedAtomicObservation.mass_positive
    (historyPMF (inventoryBound (next runtime))) (Fin.last (inventoryBound (next runtime)))
    (SourceUniformFibreVariance.source_positive _ _)
  linarith only [lower, positive]

theorem original_prior_loss (runtime : LivingRuntimeState process) (oldDepth freshDepth : Nat)
    (proposal : FieldSpace oldDepth (inventoryBound runtime)) :
    (historyPMF (inventoryBound (next runtime)) (Fin.last (inventoryBound (next runtime)))).toReal ≤
      ‖target runtime freshDepth - nextFieldRead oldDepth (inventoryBound runtime)
        (timeTransfer oldDepth (inventoryBound runtime) proposal)‖ ^ 2 := by
  rw [← SourceGeneratedJointFiniteDecoder.actor_action]
  exact prior_loss runtime freshDepth (Actor.currentPullback oldDepth (inventoryBound runtime) proposal)

end
end SourceGeneratedBornDecoder
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
