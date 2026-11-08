import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveExternalSupplySource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveExternalSupplyConsumer
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open WholeCursorLaw
open LiveExternalSupplySource
variable (old : Emitter) (saved : Cursor old)

theorem same_actual_live_state (original : saved.side = .original) :
    EventStep.seed (start old saved) = Extension.state old
      (CatalogueHandoffSource.supply old (AtomicWorkSource.catalogue old (batch old saved))) (EventStep.seed saved) :=
  CatalogueHandoffSource.seed old (AtomicWorkSource.catalogue old (batch old saved)) saved original

theorem the_selected_word_contains_real_supplier_production (front : Word) (found : offer old saved = some front) :
    WholeCursorLaw.production ∈ front := by
  have member := (selected_is_generated_from_the_actual_source old saved front found).2.1
  simp only [recipes,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl <;> simp [cycle]

theorem actual_execution_keeps_the_source_and_payment
    (enabled : Bool) (rival : Opponent (code old saved))
    (success : assess old saved enabled rival = .executed) :
    ∃ front, offer old saved = some front ∧
      (row old saved enabled rival).submitted = assembled old saved front ∧
      (EventStep.seed (next old saved enabled rival)).current =
        old.law.next (row old saved enabled rival).before.current (assembled old saved front) ∧
      (∀ item ∈ StageTrace.items (row old saved enabled rival),old.law.Valid item.before item.request) ∧
      (∀ item ∈ old.law.rawItems (old.law.next (current old saved) (assembled old saved front)) (fees old saved),
        old.law.Valid item.before item.request) := by
  have actual := AtomicWorkSource.executed_uses_the_original_whole_word old (batch old saved) saved
    (submit old saved enabled) rival success
  have available : (offer old saved).isSome = true := (Bool.and_eq_true_iff.mp actual.1).2
  cases found : offer old saved with
  | none => simp only [found,Option.isSome_none,Bool.false_eq_true] at available
  | some front =>
      have word : batch old saved = assembled old saved front := by simp only [batch,found]
      exact ⟨front,rfl,actual.2.1.trans word,
        actual.2.2.1.trans (congrArg (old.law.next (row old saved enabled rival).before.current) word),
        actual.2.2.2,(selected_is_generated_from_the_actual_source old saved front found).2.2.2.2.2⟩

abbrev rawOccurrence (enabled : Bool) (rival : Opponent (code old saved))
    (success : assess old saved enabled rival = .executed) :=
  AtomicWorkConsumer.executed_batch_has_one_raw_occurrence old (batch old saved) saved (submit old saved enabled) rival success
abbrev financialItems (enabled : Bool) (rival : Opponent (code old saved))
    (future : List (EventHistory.Stage (code := code old saved))) :=
  AtomicWorkConsumer.the_final_ledger_consumes_the_original_batch old (batch old saved) saved (submit old saved enabled) rival future
abbrev financialPrefix (original : saved.side = .original)
    (future : List (EventHistory.Stage (code := code old saved))) :=
  CatalogueHandoffSource.completeFinancialPrefix old (AtomicWorkSource.catalogue old (batch old saved)) saved original future

-- The recursive producer submits a fresh source query at each actual endpoint.
theorem recursive_step_keeps_the_actual_next (state : Snapshot) (command : Command state) :
    (step state command).cursor = next state.emitter state.cursor command.enabled command.rival ∧
      (step state command).cursor.cut = state.cursor.cut + 1 ∧
      (step state command).cursor.ownerStart = state.cursor.ownerStart := ⟨rfl,rfl,rfl⟩

abbrev native (enabled : Bool) (rival : Opponent (code old saved))
    (future : List (EventHistory.Stage (code := code old saved))) (ordinal : Nat) :=
  ProgrammeHistory.execution_face_shares_whole_ledger_and_next
    (EventHistory.execute (start old saved) ((work old saved enabled,rival)::future)).source.input ordinal
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveExternalSupplyConsumer
