import H0mework.Probability.Empirical.WeightedRecovery
import H0mework.Realization.HilbertTransfer.Composition

/-! The original actor PMF reaches the old field L² before its actual next transfer. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWeightedRecovery.Runtime.Actor

open SourceGeneratedRuntimeHistoryProbability SourceConditionalTransfer MeasureTheory
open SourceGeneratedScalarCofinalTopology.NativeProbability

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {B : Type u} [AddCommGroup B] (read : process.State → B)
variable (runtime : LivingRuntimeState process) (bound : Nat)

local instance : MeasurableSpace (Field read) := fieldBorel read

abbrev ActorSpace := Space (historyPMF bound)

theorem actor_measurePreserving :
    MeasurePreserving (fieldSample read runtime bound) (historyPMF bound).toMeasure
      (empirical read runtime bound).toMeasure := by
  refine ⟨measurable_of_finite _, ?_⟩
  exact (PMF.toMeasure_map _ _ (measurable_of_finite _)).trans
    (congrArg PMF.toMeasure (fieldPMF_from_indices read runtime bound).symm)

def actorPullback : SourceGeneratedEmpiricalHilbert.Space read runtime bound →ₗᵢ[ℂ] ActorSpace bound :=
  Lp.compMeasurePreservingₗᵢ ℂ (fieldSample read runtime bound) (actor_measurePreserving read runtime bound)

theorem actorPullback_at (value : SourceGeneratedEmpiricalHilbert.Space read runtime bound)
    (index : Fin (bound + 1)) :
    actorPullback read runtime bound value index = value (fieldSample read runtime bound index) :=
  ae_at_support (historyPMF bound) index (by simp [historyPMF])
    (Lp.coeFn_compMeasurePreserving value (actor_measurePreserving read runtime bound))

def actorTransfer : ActorSpace bound →L[ℂ] SourceGeneratedEmpiricalHilbert.Space read runtime bound :=
  IsometricRetainedTransfer.transfer (actorPullback read runtime bound)

def actorResidual : ActorSpace bound →L[ℂ] ActorSpace bound :=
  IsometricRetainedTransfer.residual (actorPullback read runtime bound)

def nextPullback : SourceGeneratedEmpiricalHilbert.Space read runtime.tick.next bound →ₗᵢ[ℂ] ActorSpace bound :=
  (actorPullback read runtime bound).comp (SourceGeneratedEmpiricalHilbert.pullback read runtime bound)

theorem nextPullback_at (value : SourceGeneratedEmpiricalHilbert.Space read runtime.tick.next bound)
    (index : Fin (bound + 1)) :
    nextPullback read runtime bound value index = value (nextAtom read runtime bound index) :=
  (actorPullback_at read runtime bound _ index).trans (pullback_at_sample read runtime bound value index)

theorem next_measurePreserving :
    MeasurePreserving (nextAtom read runtime bound) (historyPMF bound).toMeasure
      (empirical read runtime.tick.next bound).toMeasure :=
  (SourceGeneratedEmpiricalHilbert.source_measurePreserving read runtime bound).comp
    (actor_measurePreserving read runtime bound)

theorem nextPullback_is_source_map :
    nextPullback read runtime bound = Lp.compMeasurePreservingₗᵢ ℂ (nextAtom read runtime bound)
      (next_measurePreserving read runtime bound) := by
  apply LinearIsometry.ext
  intro value
  apply Lp.ext
  apply Filter.Eventually.of_forall
  intro index
  have source := ae_at_support (historyPMF bound) index (by simp [historyPMF])
    (Lp.coeFn_compMeasurePreserving value (next_measurePreserving read runtime bound))
  exact (nextPullback_at read runtime bound value index).trans source.symm

theorem complete_residual_energy (value : ActorSpace bound) :
    ‖IsometricRetainedTransfer.residual (nextPullback read runtime bound) value‖ ^ 2 =
      ‖actorResidual read runtime bound value‖ ^ 2 +
        ‖SourceGeneratedEmpiricalHilbert.residual read runtime bound (actorTransfer read runtime bound value)‖ ^ 2 :=
  IsometricRetainedTransfer.residual_comp_energy (actorPullback read runtime bound)
    (SourceGeneratedEmpiricalHilbert.pullback read runtime bound) value

end
end SourceWeightedRecovery.Runtime.Actor
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
