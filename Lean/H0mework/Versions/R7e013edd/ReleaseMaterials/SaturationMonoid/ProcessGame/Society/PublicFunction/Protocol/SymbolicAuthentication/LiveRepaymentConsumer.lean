import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveRepaymentSource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveRepaymentConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open LiveSupplySynthesisSource (Emitter Word current)
open LiveRepaymentSource
noncomputable section
variable (old : Emitter) (saved : Cursor old)

private theorem final_index (state : RecycledQuorumMaterial.Current) (word : Word) (i j : Nat) :
    (old.law.execute state i word).final = (old.law.execute state j word).final := by
  induction word generalizing state i j with
  | nil => rfl
  | cons head tail ih => exact ih (old.law.step state head) (i+1) (j+1)

theorem the_compiled_word_pays_the_original_principal (front : Word)
    (found : offer old saved = some front) :
    0 < Repayment.quantity old.law position (intermediate old saved front) ∧
      (old.law.next (current old saved) (assembled old saved front)).claims () 1 2 =
        (current old saved).claims () 1 2 - Repayment.quantity old.law position (intermediate old saved front) := by
  have selected := (the_source_offer_is_an_original_repayment_compilation old saved front found).2
  have paid := Repayment.paid_principal_balance old.law position (intermediate old saved front) selected.1
  refine ⟨selected.1.1,?_⟩
  change (old.law.execute (current old saved) 0 (assembled old saved front)).final.claims () 1 2 = _
  rw [assembled,RawLaw.execute_append]
  simp only [Nat.zero_add]
  change (old.law.execute (intermediate old saved front) front.length
    (Repayment.candidate old.law position (intermediate old saved front))).final.claims () 1 2 = _
  rw [final_index old _ _ front.length 0]
  change (old.law.next (intermediate old saved front)
    (Repayment.candidate old.law position (intermediate old saved front))).claims () 1 2 = _
  rw [paid,selected.2.1]
  rfl

variable (enabled : Bool) (rival : Opponent (code old saved))
theorem executed_repayment_strictly_reduces_the_same_original_debt (original : saved.side = .original)
    (success : assess old saved enabled rival = .executed) :
    ∃ front, offer old saved = some front ∧
      (row old saved enabled rival).submitted = assembled old saved front ∧
      0 < Repayment.quantity old.law position (intermediate old saved front) ∧
      (EventStep.seed (next old saved enabled rival)).current.claims () 1 2 =
        (current old saved).claims () 1 2 - Repayment.quantity old.law position (intermediate old saved front) ∧
      (EventStep.seed (next old saved enabled rival)).current.claims () 1 2 < (current old saved).claims () 1 2 := by
  have actual := AtomicWorkSource.executed_uses_the_original_whole_word old (batch old saved) saved
    (submit old saved enabled) rival success
  have available : enabled = true ∧ (offer old saved).isSome = true := by
    simpa only [submit,Bool.and_eq_true] using actual.1
  cases found : offer old saved with
  | none => simp [found] at available
  | some front =>
    have word : batch old saved = assembled old saved front := by simp [batch,found]
    have submitted := actual.2.1.trans word
    have endpoint := actual.2.2.1
    change (EventStep.seed (next old saved enabled rival)).current =
      old.law.next (EventStep.seed (start old saved)).current (batch old saved) at endpoint
    rw [seed_is_the_same_actual_current old saved original] at endpoint
    have final := endpoint.trans (congrArg (old.law.next (current old saved)) word)
    have debt := the_compiled_word_pays_the_original_principal old saved front found
    have same := (congrArg (fun state => state.claims () 1 2) final).trans debt.2
    exact ⟨front,rfl,submitted,debt.1,same,by rw [same];exact sub_lt_self _ debt.1⟩

theorem the_final_native_ledger_consumes_the_actual_repayment
    (future : List (EventHistory.Stage (code := code old saved))) :
    let final := EventHistory.execute (start old saved)
      ((AtomicWorkSource.protocol old (batch old saved) (submit old saved enabled),rival)::future)
    (Financial.inventoryAt final.source.input (ProgrammeHistory.visitAt final.source.input
      (EventStep.boundary (start old saved)))).filterMap
      (Financial.InstructionOrigin.instruction? final.source.input) = StageTrace.items (row old saved enabled rival) :=
  AtomicWorkConsumer.the_final_ledger_consumes_the_original_batch old (batch old saved) saved
    (submit old saved enabled) rival future
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveRepaymentConsumer
