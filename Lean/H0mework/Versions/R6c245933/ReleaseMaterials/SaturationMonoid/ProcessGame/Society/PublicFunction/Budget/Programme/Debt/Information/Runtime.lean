import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Source

set_option autoImplicit false
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Runtime

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
  (views : List (View (code := model.source.code)))
  (point : Cursor model.source.code) (template : Template (code := model.source.code))
  (selected : Activation template)

abbrev bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) :=
  ⟨model.base,model.scope,Information.target views template selected point,model.law_exact,model.task_exact⟩

abbrev facade := Native.AuthorityRuntime.facade (bound model views point template selected)

def activated : LivingRuntimeState (Native.AuthorityRuntime.process (bound model views point template selected)) :=
  (facade model views point template selected).seed.advance (depth point+1)

private theorem activated_state :
    (activated model views point template selected).state = depth point+1 := by
  have all (n : Nat) : ((facade model views point template selected).seed.advance n).state = n := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg Nat.succ ih
  exact all _

def native : Native.Authority.Disposition (bound model views point template selected) (depth point) :=
  match (facade model views point template selected).readoutAt (activated model views point template selected) .responsibilities with
  | .inl actual => actual.2 (depth point) (by
      change (ProgrammeHistory.visitAt (Information.target views template selected point).input
        (activated model views point template selected).state).current = _
      rw [activated_state]
      rfl)
  | .inr impossible => nomatch impossible

theorem the_original_root_consumes_locally_generated_actual_work_and_next :
    let actual := activated model views point template selected
    (actualExecution views template selected point).submitted =
      (if (seed point).remaining = 0 then [] else
        model.source.code.action (policy views template selected.site) selected.site
          ((seed point).frame.inbox selected.site)) ∧
      (∀ ordinal ≤ arrival point,Native.Coupling.Match model.source.code point.source.input
        (Information.target views template selected point).input (Financial.accountAt point.source.input ordinal)
        (Financial.accountAt (Information.target views template selected point).input ordinal)) ∧
      (native model views point template selected).joint.finance =
        Financial.accountAt (Information.target views template selected point).input (arrival point+1) ∧
      HEq ((facade model views point template selected).readoutAt actual .responsibilities)
        (actual.tick.generated.projectionOutcome (.component ())) ∧
      HEq actual.tick.generated.wholeLedgerWriteBack
        (actual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt actual.current.visit.current) ∧
      actual.tick.nextCurrent = (facade model views point template selected).process.stateAt
        ((facade model views point template selected).process.successor actual.state) := by
  let actual := activated model views point template selected
  have rooted := (facade model views point template selected).readoutAt_factorizes actual .responsibilities
  exact ⟨the_actual_activation_submits_only_locally_recovered_work views template selected point,
    actual_recovery_preserves_the_full_original_financial_prefix views template selected point,
    by
      rw [(native model views point template selected).joint_exact]
      have exactAccount := (Native.generate (Information.target views template selected point) (depth point)).finance_exact
      have address : depth point+2 = arrival point+1 := by dsimp only [depth,arrival];omega
      rw [address] at exactAccount
      exact exactAccount,
    rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Runtime
