import H0mework.Fock.PrimeFieldCalculation.CalculationFrontier

/-! Query cells and their recovery readout are taken from the source-fixed calculation history. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeCalculation

open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
open SourcePrimeHistoryRecovery
open SourceGeneratedRuntimeHistoryProbability

noncomputable section

def recordedQuery (bound : Nat) (actor : Fin (bound + 1)) : Raw sourceOwner bound := fun time =>
  rawField (((frontier bound).history.stageAt (cell sourceOwner bound actor time)).next.state)

theorem recorded_is_query (bound : Nat) (actor : Fin (bound + 1)) :
    recordedQuery bound actor = observe sourceOwner bound actor := by
  funext time
  exact (query_is_material sourceOwner bound actor time).symm

theorem recorded_recovers (bound : Nat) (task : Fin (bound + 1) → ℂ) (actor : Fin (bound + 1)) :
    decoder sourceOwner bound task (recordedQuery bound actor) = task actor := by
  rw [recorded_is_query, decoder_query]

theorem last_record_is_target (bound : Nat) :
    recordedQuery bound (Fin.last bound) (Fin.last (windowBound sourceOwner bound)) =
      rawField (normal bound).targetRuntime.state := rfl

theorem last_record_is_generated_birth (bound : Nat) :
    let current : CanonicalUnitArithmeticRoot.Current :=
      (runtimeAt (completionDepth sourceOwner bound)).current.visit.current
    recordedQuery bound (Fin.last bound) (Fin.last (windowBound sourceOwner bound)) =
      sourceFieldAt current + SourceFactorizationAction.Fock.birth current := by
  have localOperation := (realization bound).operationAt (Fin.last (completionDepth sourceOwner bound))
  have source := localOperation.2.2.1
  rw [recorded_is_query, SourcePrimeHistoryRecovery.query_value]
  change rawField (bound + 1 + windowBound sourceOwner bound) = _
  rw [show bound + 1 + windowBound sourceOwner bound = completionDepth sourceOwner bound + 1 by
    unfold completionDepth; omega]
  exact source

end
end SourcePrimeCalculation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
