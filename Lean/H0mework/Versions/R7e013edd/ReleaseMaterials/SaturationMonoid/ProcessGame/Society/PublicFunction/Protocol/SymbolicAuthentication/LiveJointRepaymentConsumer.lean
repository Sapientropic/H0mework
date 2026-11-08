import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveJointRepaymentSource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveJointRepaymentConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open LiveSupplySynthesisSource (Emitter Word current)
open LiveJointRepaymentSource
noncomputable section
variable (old : Emitter) (saved : Cursor old)

theorem the_generated_payment_reduces_original_principal_and_retains_original_fees (front : Word)
    (found : offer old saved = some front) :
    0 < quantity old saved front ∧
      (old.law.next (current old saved) (assembled old saved front)).claims () 1 2 =
        (current old saved).claims () 1 2 - quantity old saved front ∧
      ∀ item ∈ old.law.rawItems (old.law.next (current old saved) (assembled old saved front)) (fees old saved),
        old.law.Valid item.before item.request := by
  have selected := (selected_is_computed_from_the_original_supply_and_delivery_words old saved front found).2
  refine ⟨selected.1,?_,selected.2.2.2.2⟩
  change (old.law.execute (current old saved) 0 (assembled old saved front)).final.claims () 1 2 = _
  rw [assembled,RawLaw.execute_append]
  change (old.law.step (beforePayment old saved front) (payment old saved front)).claims () 1 2 = _
  rw [RawLaw.step,if_pos selected.2.2.1]
  change (beforePayment old saved front).claims () 1 2 - quantity old saved front = _
  exact congrArg (fun balance => balance - quantity old saved front) selected.2.1

variable (enabled : Bool) (rival : Opponent (code old saved))
theorem actual_repayment_and_fee_capacity_share_the_same_next (original : saved.side = .original)
    (success : assess old saved enabled rival = .executed) :
    ∃ front, offer old saved = some front ∧ (row old saved enabled rival).submitted = assembled old saved front ∧
      (EventStep.seed (next old saved enabled rival)).current.claims () 1 2 =
        (current old saved).claims () 1 2 - quantity old saved front ∧
      (EventStep.seed (next old saved enabled rival)).current.claims () 1 2 < (current old saved).claims () 1 2 ∧
      ∀ item ∈ old.law.rawItems (EventStep.seed (next old saved enabled rival)).current (fees old saved),
        old.law.Valid item.before item.request := by
  have actual := AtomicWorkSource.executed_uses_the_original_whole_word old (batch old saved) saved
    (submit old saved enabled) rival success
  have available : enabled = true ∧ (offer old saved).isSome = true := by
    simpa only [submit,Bool.and_eq_true] using actual.1
  cases found : offer old saved with
  | none => simp [found] at available
  | some front =>
    have word : batch old saved = assembled old saved front := by simp [batch,found]
    have endpoint := actual.2.2.1
    change (EventStep.seed (next old saved enabled rival)).current =
      old.law.next (EventStep.seed (start old saved)).current (batch old saved) at endpoint
    rw [seed_is_the_same_actual_current old saved original] at endpoint
    have final := endpoint.trans (congrArg (old.law.next (current old saved)) word)
    have generated := the_generated_payment_reduces_original_principal_and_retains_original_fees old saved front found
    have debt := (congrArg (fun state => state.claims () 1 2) final).trans generated.2.1
    refine ⟨front,rfl,actual.2.1.trans word,debt,?_,?_⟩
    · rw [debt];exact sub_lt_self _ generated.1
    · rw [final];exact generated.2.2

theorem all_future_stages_retain_the_actual_financial_visit
    (future : List (EventHistory.Stage (code := code old saved))) :
    let final := EventHistory.execute (start old saved)
      ((AtomicWorkSource.protocol old (batch old saved) (submit old saved enabled),rival)::future)
    (Financial.inventoryAt final.source.input (ProgrammeHistory.visitAt final.source.input
      (EventStep.boundary (start old saved)))).filterMap
      (Financial.InstructionOrigin.instruction? final.source.input) = StageTrace.items (row old saved enabled rival) :=
  AtomicWorkConsumer.the_final_ledger_consumes_the_original_batch old (batch old saved) saved
    (submit old saved enabled) rival future
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveJointRepaymentConsumer
