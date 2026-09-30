import H0mework.Fock.HistoryModel.OriginalHilbertRecovery
import H0mework.Fock.PrimeFieldCalculation.CalculationQuery

/-! The finite word restriction reads the original source-controlled query cells. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.OriginalHilbert.Recorded

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed SourcePrimeHistoryRecovery
open NoIslandNoMagic.CanonicalArithmeticState ParticleWaveFock ParticleWaveFockRuntime

noncomputable section

def recordedRestriction (depth bound : Nat) (value : Field nativeStep (rawWords depth)) :
    Raw sourceOwner bound := fun time =>
  thetaProjection (completeRead (Fock.actions depth) (Fock.observer depth) (.inl ())
    (List.replicate time.val (.inl ())) ((originalField depth).symm value) 0)

theorem recordedRestriction_nextRead (depth bound : Nat) (actor : Fin (bound + 1)) :
    recordedRestriction depth bound (Actor.nextRead depth bound actor) =
      SourcePrimeCalculation.recordedQuery bound actor := by
  funext time
  have original : (originalField depth).symm (Actor.nextRead depth bound actor) =
      Complete.point depth ((runtimeAt (actor.val + 1)).current.visit.current : Current) :=
    (congrArg (originalField depth).symm (next_read_actual depth bound actor)).trans
      ((originalField depth).symm_apply_apply _)
  have recorded := congrFun (SourcePrimeCalculation.recorded_is_query bound actor) time
  have queryValue := SourcePrimeHistoryRecovery.query_value sourceOwner bound actor time
  exact (congrArg (fun point => thetaProjection (completeRead (Fock.actions depth) (Fock.observer depth) (.inl ())
      (List.replicate time.val (.inl ())) point 0)) original).trans
    ((Dynamic.Hilbert.native_word_theta depth time.val (actor.val + 1)).trans
      (recorded.trans queryValue).symm)

end
end SourceGeneratedActionWords.Fock.OriginalHilbert.Recorded
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
