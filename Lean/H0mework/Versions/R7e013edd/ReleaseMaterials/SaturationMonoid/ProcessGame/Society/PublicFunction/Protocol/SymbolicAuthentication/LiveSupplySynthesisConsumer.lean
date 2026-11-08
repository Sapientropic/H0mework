import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveSupplySynthesisSource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveSupplySynthesisConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open LiveSupplySynthesisSource
noncomputable section
variable (old : Emitter) (saved : Cursor old) (enabled : Bool) (rival : Opponent (code old saved))

theorem actual_supply_is_a_paid_original_word_and_increases_service (original : saved.side = .original)
    (success : assess old saved enabled rival = .executed) :
    (row old saved enabled rival).submitted ∈ recipes ∧
      (∀ item ∈ old.law.rawItems (current old saved) (row old saved enabled rival).submitted,
        old.law.Valid item.before item.request) ∧
      (EventStep.seed (next old saved enabled rival)).current =
        old.law.next (current old saved) (row old saved enabled rival).submitted ∧
      (current old saved).stock 1 .service < (EventStep.seed (next old saved enabled rival)).current.stock 1 .service := by
  have actual := AtomicWorkSource.executed_uses_the_original_whole_word old (batch old saved) saved
    (submit old saved enabled) rival success
  have pair : enabled = true ∧ (offer old saved).isSome = true := by
    simpa only [submit,Bool.and_eq_true] using actual.1
  have available := pair.2
  cases found : offer old saved with
  | none => simp [found] at available
  | some word =>
    have selected := offered_word_is_original_legal_and_productive old saved word found
    have batchEq : batch old saved = word := by simp [batch,found]
    have submitted := actual.2.1.trans batchEq
    have endpoint := actual.2.2.1
    change (EventStep.seed (next old saved enabled rival)).current =
      old.law.next (EventStep.seed (start old saved)).current (batch old saved) at endpoint
    rw [seed_is_the_same_actual_current old saved original] at endpoint
    have endword := endpoint.trans (congrArg (old.law.next (current old saved)) batchEq)
    rw [submitted]
    exact ⟨selected.2.1,selected.2.2.2.1,endword,by rw [endword];exact selected.2.2.2.2⟩

theorem the_native_ledger_consumes_the_same_actual_supply
    (future : List (EventHistory.Stage (code := code old saved))) :
    let final := EventHistory.execute (start old saved)
      ((AtomicWorkSource.protocol old (batch old saved) (submit old saved enabled),rival)::future)
    (Financial.inventoryAt final.source.input (ProgrammeHistory.visitAt final.source.input
      (EventStep.boundary (start old saved)))).filterMap
      (Financial.InstructionOrigin.instruction? final.source.input) = StageTrace.items (row old saved enabled rival) :=
  AtomicWorkConsumer.the_final_ledger_consumes_the_original_batch old (batch old saved) saved
    (submit old saved enabled) rival future

theorem no_offer_is_an_exhausted_source_menu (needed : demand (current old saved))
    (absent : offer old saved = none) :
    ∀ word ∈ recipes, ¬ productive old.law (current old saved) word := by
  unfold offer at absent
  rw [if_pos needed] at absent
  intro word listed paid
  exact List.find?_eq_none.mp absent word listed (decide_eq_true paid)
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveSupplySynthesisConsumer
