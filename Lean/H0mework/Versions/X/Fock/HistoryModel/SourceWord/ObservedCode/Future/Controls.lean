import H0mework.Versions.X.Fock.HistoryModel.SourceWord.ObservedCode.Future.Risk

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordFutureBit

open SourceGeneratedActionWords
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceConditionalModel (Actors)
open SourceGeneratedAcquisitionContinuation ArithmeticGeneration
open SourceGeneratedRuntimeHistoryProbability
open scoped Classical
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
noncomputable section

theorem actual_distinct_actors_same_future :
    futureRead (runtimeAt 3) [] (⟨0, by decide⟩ : Actors (runtimeAt 3)) =
      futureRead (runtimeAt 3) [] (⟨2, by decide⟩ : Actors (runtimeAt 3)) := by
  apply (future_kernel _ _ _ _).mpr
  decide

theorem actual_distinct_actors_different_future :
    futureRead (runtimeAt 3) [] (⟨0, by decide⟩ : Actors (runtimeAt 3)) ≠
      futureRead (runtimeAt 3) [] (⟨1, by decide⟩ : Actors (runtimeAt 3)) := by
  intro same
  have bitSame := (future_kernel _ _ _ _).mp same
  have unequal : SourceWordObservedCode.sourceQuery (runtimeAt 3) []
      (⟨0, by decide⟩ : Actors (runtimeAt 3)) ≠
      SourceWordObservedCode.sourceQuery (runtimeAt 3) []
        (⟨1, by decide⟩ : Actors (runtimeAt 3)) := by decide
  exact unequal bitSame

theorem actual_future_strictly_coarser_than_whole_model :
    futureRead (runtimeAt 3) [] (⟨0, by decide⟩ : Actors (runtimeAt 3)) =
      futureRead (runtimeAt 3) [] (⟨2, by decide⟩ : Actors (runtimeAt 3)) ∧
    SourceWordMinimalCode.wordRead (runtimeAt 3) []
        (⟨0, by decide⟩ : Actors (runtimeAt 3)) ≠
      SourceWordMinimalCode.wordRead (runtimeAt 3) []
        (⟨2, by decide⟩ : Actors (runtimeAt 3)) := by
  constructor
  · exact actual_distinct_actors_same_future
  · intro same
    have actorsSame := SourceWordMinimalCode.wordRead_injective (runtimeAt 3) [] same
    have actorsUnequal : (⟨0, by decide⟩ : Actors (runtimeAt 3)) ≠
      (⟨2, by decide⟩ : Actors (runtimeAt 3)) := by decide
    exact actorsUnequal actorsSame

/-- The actual nonunit copy has even source material and erases the bit while
the original G and full word carrier remain source-accounted. -/
theorem actual_copyOne_erases_future_bit (bit : ZMod 2) :
    bitAction (inventoryBound (runtimeAt 3) + 1)
      SourceWordDynamicNext.copyOne bit = 0 := by
  fin_cases bit <;> decide


end
end SourceWordFutureBit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
