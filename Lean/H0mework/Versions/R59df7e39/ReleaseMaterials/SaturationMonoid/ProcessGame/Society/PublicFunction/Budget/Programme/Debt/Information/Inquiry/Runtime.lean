import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Source

set_option autoImplicit false
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Runtime

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
  (selected : Activation template) (rival : Opponent model.source.code) (n : Nat)

def readState (authority : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (index : Nat) :
    LivingRuntimeState (Native.AuthorityRuntime.process authority) :=
  (Native.AuthorityRuntime.facade authority).seed.advance (index+1)

theorem readState_state (authority : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (index : Nat) :
    (readState authority index).state = index+1 := by
  have all (n : Nat) : ((Native.AuthorityRuntime.facade authority).seed.advance n).state = n := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg Nat.succ ih
  exact all _

def read (authority : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (index : Nat) : Native.Authority.Disposition authority index :=
  match (Native.AuthorityRuntime.facade authority).readoutAt (readState authority index) .responsibilities with
  | .inl actual => actual.2 index (by
      change (ProgrammeHistory.visitAt authority.source.input (readState authority index).state).current = _
      rw [readState_state]
      rfl)
  | .inr impossible => nomatch impossible

abbrev bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) :=
  ⟨model.base,model.scope,Inquiry.target views template selected point rival,
    by cases result : compile views template selected.site <;> exact model.law_exact,
    by cases result : compile views template selected.site <;> exact model.task_exact⟩

abbrev facade := Native.AuthorityRuntime.facade (bound model views point template selected rival)

def activated : LivingRuntimeState (Native.AuthorityRuntime.process (bound model views point template selected rival)) :=
  (facade model views point template selected rival).seed.advance (depth point+n+1)

abbrev native : Native.Authority.Disposition (bound model views point template selected rival) (depth point+n) :=
  read (bound model views point template selected rival) (depth point+n)

theorem the_original_root_consumes_autonomous_inquiry_ledger_and_next :
    let actual := activated model views point template selected rival n
    (actualExecution views template selected point rival n).submitted =
      Feedback.word model.source.code
        ((Inquiry.target views template selected point rival).feedbackPolicy (point.cut+n))
        (entry views template selected point rival) (state views template selected point rival n) ∧
      (∀ ordinal ≤ arrival point,Native.Coupling.Match model.source.code point.source.input
        (Inquiry.target views template selected point rival).input (Financial.accountAt point.source.input ordinal)
        (Financial.accountAt (Inquiry.target views template selected point rival).input ordinal)) ∧
      (native model views point template selected rival n).joint.finance =
        Financial.accountAt (Inquiry.target views template selected point rival).input (arrival point+n+1) ∧
      HEq ((facade model views point template selected rival).readoutAt actual .responsibilities)
        (actual.tick.generated.projectionOutcome (.component ())) ∧
      HEq actual.tick.generated.wholeLedgerWriteBack
        (actual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt actual.current.visit.current) ∧
      actual.tick.nextCurrent = (facade model views point template selected rival).process.stateAt
        ((facade model views point template selected rival).process.successor actual.state) := by
  let actual := activated model views point template selected rival n
  have rooted := (facade model views point template selected rival).readoutAt_factorizes actual .responsibilities
  exact ⟨the_actual_word_is_generated_by_the_original_protocol_state views template selected point rival n,
    the_complete_original_financial_prefix_is_preserved views template selected point rival,
    by
      rw [(native model views point template selected rival n).joint_exact]
      have exactAccount := (Native.generate (Inquiry.target views template selected point rival) (depth point+n)).finance_exact
      have address : depth point+n+2 = arrival point+n+1 := by dsimp only [depth,arrival];omega
      rw [address] at exactAccount
      exact exactAccount,
    rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Runtime
