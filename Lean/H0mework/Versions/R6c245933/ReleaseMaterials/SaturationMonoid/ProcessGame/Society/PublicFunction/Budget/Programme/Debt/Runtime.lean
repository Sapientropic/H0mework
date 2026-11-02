import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Source

set_option autoImplicit false
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Runtime

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (point : Cursor model.source.code) (origin : Origin point) (template : Template (code := model.source.code))
  (selected : Activation template)

abbrev bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) :=
  ⟨model.base,model.scope,target point origin template selected,model.law_exact,model.task_exact⟩

abbrev facade := Native.AuthorityRuntime.facade (bound model point origin template selected)

def activated : LivingRuntimeState (Native.AuthorityRuntime.process (bound model point origin template selected)) :=
  (facade model point origin template selected).seed.advance (depth point+1)

private theorem activated_state :
    (activated model point origin template selected).state = depth point+1 := by
  have all (n : Nat) : ((facade model point origin template selected).seed.advance n).state = n := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg Nat.succ ih
  exact all _

def native : Native.Authority.Disposition (bound model point origin template selected) (depth point) :=
  match (facade model point origin template selected).readoutAt (activated model point origin template selected) .responsibilities with
  | .inl actual => actual.2 (depth point) (by
      change (ProgrammeHistory.visitAt (target point origin template selected).input
        (activated model point origin template selected).state).current = _
      rw [activated_state]
      rfl)
  | .inr impossible => nomatch impossible

theorem the_original_root_consumes_the_residual_generated_actual_word_and_next :
    let actual := activated model point origin template selected
    (execution point origin template selected).submitted =
      (if (seed point).remaining = 0 then [] else
        if model.source.code.memoryReady ((seed point).frame.inbox selected.site) then word point origin template else []) ∧
      (∀ ordinal ≤ arrival point,Native.Coupling.Match model.source.code point.source.input
        (target point origin template selected).input (Financial.accountAt point.source.input ordinal)
        (Financial.accountAt (target point origin template selected).input ordinal)) ∧
      (native model point origin template selected).joint.finance =
        Financial.accountAt (target point origin template selected).input (arrival point+1) ∧
      (∀ index : OldSlot point origin,∀ event ∈ (actualFollow point origin template selected index).path.events
        (target point origin template selected).input, event.Lawful (target point origin template selected).input) ∧
      HEq ((facade model point origin template selected).readoutAt actual .responsibilities)
        (actual.tick.generated.projectionOutcome (.component ())) ∧
      HEq actual.tick.generated.wholeLedgerWriteBack
        (actual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt actual.current.visit.current) ∧
      actual.tick.nextCurrent = (facade model point origin template selected).process.stateAt
        ((facade model point origin template selected).process.successor actual.state) := by
  let actual := activated model point origin template selected
  have rooted := (facade model point origin template selected).readoutAt_factorizes actual .responsibilities
  exact ⟨the_generated_word_is_actually_submitted point origin template selected,
    the_full_original_financial_prefix_is_preserved point origin template selected,
    by
      rw [(native model point origin template selected).joint_exact]
      have exactAccount := (Native.generate (target point origin template selected) (depth point)).finance_exact
      have address : depth point+2 = arrival point+1 := by dsimp only [depth,arrival];omega
      rw [address] at exactAccount
      exact exactAccount,
    fun index => (actualFollow point origin template selected index).path.receipts_are_lawful _,
    rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Runtime
