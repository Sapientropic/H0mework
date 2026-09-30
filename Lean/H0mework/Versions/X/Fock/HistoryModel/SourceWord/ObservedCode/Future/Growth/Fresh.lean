import H0mework.Versions.X.Fock.HistoryModel.SourceWord.ObservedCode.Future.Growth.Transport

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordFutureBitGrowth

open SourceGeneratedActionWords
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceConditionalModel (Actors)
open SourceGeneratedAcquisitionContinuation ArithmeticGeneration
open SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
noncomputable section

theorem fresh_bit_action (depth : Nat) (bit : ZMod 2) :
    SourceWordFutureBit.bitAction (depth + 1)
        (.inr (FamilyModel.Fock.newestIndex depth)) bit =
      bit * SourceWordObservedCode.observe
        ((runtimeAt depth).tick.next.current.visit.current : Current) := by
  change bit * (scanIndex (NativeCopy.Fock.material (depth + 1)
    (FamilyModel.Fock.newestIndex depth)) : ZMod 2) = _
  rw [SourceGeneratedActionWords.Fock.Dynamic.newest_material_actual]
  rfl

theorem fresh_next_observed (depth : Nat) :
    SourceWordObservedCode.observe
      (NativeCopy.copy ((runtimeAt depth).tick.next.current.visit.current : Current)
        ((runtimeAt depth).tick.next.current.visit.current : Current)) =
      SourceWordFutureBit.bitAction (depth + 1)
        (.inr (FamilyModel.Fock.newestIndex depth))
        (SourceWordObservedCode.observe
          ((runtimeAt depth).tick.next.current.visit.current : Current)) := by
  rw [← SourceGeneratedActionWords.Fock.Dynamic.newest_material_actual depth]
  exact SourceWordFutureBit.step_observe (depth + 1)
    (.inr (FamilyModel.Fock.newestIndex depth))
    (NativeCopy.Fock.material (depth + 1) (FamilyModel.Fock.newestIndex depth))

theorem fresh_complete_action_is_source_step (depth : Nat) :
    Fock.Complete.action (depth + 1) (.inr (FamilyModel.Fock.newestIndex depth))
        (Fock.Complete.nativeNext depth) =
      Fock.Complete.point (depth + 1)
        (Fock.step (depth + 1) (.inr (FamilyModel.Fock.newestIndex depth))
          ((runtimeAt depth).tick.next.current.visit.current : Current)) := by
  simpa only [Fock.step, SourceGeneratedActionWords.Fock.Dynamic.newest_material_actual]
    using SourceGeneratedActionWords.Fock.Dynamic.fresh_letter_execution depth

theorem fresh_read_at_next (depth : Nat) :
    SourceWordObservedCode.readAt depth
        [(.inr (FamilyModel.Fock.newestIndex depth) : Fock.Letter (depth + 1))] depth =
      SourceWordFutureBit.bitAction (depth + 1)
        (.inr (FamilyModel.Fock.newestIndex depth))
        (SourceWordObservedCode.readAt depth [] depth) := by
  change SourceWordObservedCode.observe
      (Fock.step (depth + 1) (.inr (FamilyModel.Fock.newestIndex depth))
        (nativeStep ((runtimeAt depth).current.visit.current : Current))) = _
  exact SourceWordFutureBit.step_observe (depth + 1)
    (.inr (FamilyModel.Fock.newestIndex depth))
    (nativeStep ((runtimeAt depth).current.visit.current : Current))

theorem fresh_read_at_next_material (depth : Nat) :
    SourceWordObservedCode.readAt depth
        [(.inr (FamilyModel.Fock.newestIndex depth) : Fock.Letter (depth + 1))] depth =
      SourceWordObservedCode.readAt depth [] depth *
        SourceWordObservedCode.observe
          ((runtimeAt depth).tick.next.current.visit.current : Current) := by
  rw [fresh_read_at_next, fresh_bit_action]


end
end SourceWordFutureBitGrowth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
