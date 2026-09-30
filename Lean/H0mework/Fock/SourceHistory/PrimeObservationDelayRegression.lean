import H0mework.Fock.PrimeField.DelayRecovery

/-! No fixed finite raw window can replace the same complete Model on all original native occurrences. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeObservationDelay

open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open SourcePrimeHistoryRecovery
open SourceGeneratedActionObservationHistory SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery

noncomputable section

theorem no_fixed_window_model (width : Nat) :
    ¬ ∃ recover : (Fin (width + 1) → IntegralOneParticle) → Model nativeAction observation,
      ∀ runtime : LivingRuntimeState process,
        recover (FiniteRecurrence.Native.rawWindow (process := process) rawField width runtime) =
          SourceOperationNative.Observed.modelPoint (process := process) rawField runtime := by
  rintro ⟨recover, exactRead⟩
  let runtime := startRuntime sourceOwner 1 width
  let first : Fin 2 := 0
  let second : Fin 2 := 1
  have sameQuery : shortQuery sourceOwner 1 width first = shortQuery sourceOwner 1 width second :=
    (query_constant sourceOwner 1 width first).trans (query_constant sourceOwner 1 width second).symm
  have firstRead := exactRead ((history runtime 1).stageAt first).next
  have secondRead := exactRead ((history runtime 1).stageAt second).next
  have sameModel := firstRead.symm.trans ((congrArg recover sameQuery).trans secondRead)
  have atoms := (SourceConditionalRecovery.nextAtom_model_iff (process := process) rawField runtime 1 first second).mpr sameModel
  have indices := full_next_injective sourceOwner runtime 1 atoms
  exact (by decide : (0 : Fin 2) ≠ 1) indices

theorem one_actor_zero_cost (owner : GlobalParentOwner) (width : Nat) :
    error (historyPMF 0) (shortQuery owner 0 width) (clockTask owner 0 width)
      (fun _ => (firstState owner width : ℂ)) = 0 := by
  simpa only [Nat.zero_add, Nat.cast_zero, zero_div, add_zero, zero_mul, Complex.ofReal_natCast] using minimum_clock_cost owner 0 width

theorem every_width_has_positive_cost (width : Nat) :
    ∀ decode : (Fin (width + 1) → IntegralOneParticle) → ℂ,
      0 < Runtime.Actor.rawError (process := process) rawField (startRuntime sourceOwner 1 width) 1 (clockTask sourceOwner 1 width)
        (fun field => decode (FiniteRecurrence.Native.fieldRead (process := process) rawField width field)) :=
  clock_cost_positive sourceOwner 1 width (by decide)

end
end SourcePrimeObservationDelay
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
