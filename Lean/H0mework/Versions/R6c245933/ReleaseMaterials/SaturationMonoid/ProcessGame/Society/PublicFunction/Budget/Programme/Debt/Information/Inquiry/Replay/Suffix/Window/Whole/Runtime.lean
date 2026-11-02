import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Complete
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Review

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Runtime

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument} {fuel : Nat}

def execute (point : Cursor code) (original : Distributed.Recall.Information.Agency.Protocol.Rule code)
    (program : Program code fuel) (rival : Opponent code) : Cursor code :=
  let next := source point original program rival
  ⟨next.reference,next.reference_generated,next.history,next.original,next.opponent,next.side,
    entry point original program rival,next.feedbackOverrides,
    point.cut+Cut.horizon point.source point.entry point.cut,point.ownerStart⟩

theorem every_stage_runs_in_the_one_actual_source (point : Cursor code)
    (original : Distributed.Recall.Information.Agency.Protocol.Rule code) (program : Program code fuel)
    (rival : Opponent code) (offset : Nat) :
    (execute point original program rival).source.feedbackState (execute point original program rival).entry (point.cut+offset) =
      Residual.run code (Residual.scheduleAt point.source point.cut (schedule point original program).val)
        ⟨controller point original program rival,point.entry.budget⟩ (seed point) offset :=
  Continuation.Whole.the_complete_program_runs_in_its_own_actual_source point original program rival offset

theorem the_whole_word_consumes_exactly_its_original_remaining_budget (point : Cursor code)
    (original : Distributed.Recall.Information.Agency.Protocol.Rule code) (program : Program code fuel)
    (rival : Opponent code) : (seed (execute point original program rival)).remaining = 0 := by
  rw [show seed (execute point original program rival) = Residual.run code
      (Residual.scheduleAt point.source point.cut (schedule point original program).val)
      ⟨controller point original program rival,point.entry.budget⟩ (seed point)
      (Cut.horizon point.source point.entry point.cut) from every_stage_runs_in_the_one_actual_source point original program rival _,
    Residual.remaining_is_the_seed_budget]
  exact Nat.sub_self _

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem old_refusal (policy : Option code.Policy) (input : Input code) (state : State code)
    (refused : state.frame.localLegal = false) :
    (Feedback.advance code policy input state).frame.localLegal = false := by
  cases policy with
  | none => exact refused
  | some policy =>
      cases chosen : decision code input state with
      | none => simpa only [Feedback.advance,chosen] using refused
      | some event =>
          rcases event with ⟨event,original⟩
          cases event with
          | adversary => simpa only [Feedback.advance,chosen,stepLocal,Code.step] using refused
          | activate | send => simp only [Feedback.advance,chosen,stepLocal,Code.step,refused,Bool.false_and]
          | deliver address =>
              simp only [Feedback.advance,chosen,stepLocal,Code.step]
              cases state.frame.sent[address]? <;> simp only [refused,Bool.false_and]

theorem the_whole_word_never_erases_the_historical_refusal (point : Cursor code)
    (original : Distributed.Recall.Information.Agency.Protocol.Rule code) (program : Program code fuel)
    (rival : Opponent code) (refused : (seed point).frame.localLegal = false) :
    (seed (execute point original program rival)).frame.localLegal = false := by
  rw [show seed (execute point original program rival) = Residual.run code
      (Residual.scheduleAt point.source point.cut (schedule point original program).val)
      ⟨controller point original program rival,point.entry.budget⟩ (seed point)
      (Cut.horizon point.source point.entry point.cut) from every_stage_runs_in_the_one_actual_source point original program rival _]
  have invariant (count : Nat) : (Residual.run code
      (Residual.scheduleAt point.source point.cut (schedule point original program).val)
      ⟨controller point original program rival,point.entry.budget⟩ (seed point) count).frame.localLegal = false := by
    induction count with
    | zero => exact refused
    | succ count ih => exact old_refusal _ _ _ ih
  exact invariant _

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code))
  (original : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
  (reference : Complete.FiniteProgram model.source.code)

abbrev normalized := clip (horizon domain) reference.2
abbrev plan := Review.compile model domain original (normalized model domain reference)

/-- Preparation consumes the public domain and original programme, never an actual
    world or its adaptive opponent. The complete search bound is generated here. -/
structure Prepared where
  outcome : Selection.Outcome model domain original (normalized model domain reference)
  compiled : outcome = plan model domain original reference

def prepare : Prepared model domain original reference := ⟨plan model domain original reference,rfl⟩

theorem the_whole_finite_program_contract_is_generated :
    Complete.Contract model domain original (normalized model domain reference) (plan model domain original reference) :=
  Complete.every_generated_outcome_covers_all_finite_programs model domain original (Nat.le_refl _) _ _

variable {model domain original reference}

namespace Prepared

def finish (prepared : Prepared model domain original reference) (point : Replanning.Point model domain)
    (rival : Opponent model.source.code) : Cursor model.source.code :=
  match prepared.outcome with
  | .selected choice => execute point.val original choice.policy.protocol rival
  | .blocked _ => point.val

abbrev bound (prepared : Prepared model domain original reference) (point : Replanning.Point model domain)
    (rival : Opponent model.source.code) := Replanning.native model (prepared.finish point rival)

end Prepared

variable (prepared : Prepared model domain original reference)
  (point : Replanning.Point model domain) (rival : Opponent model.source.code)

/-- This is comparison of the entire actually installed word at the original cut;
    no conjunction of separately accepted cut plans is used. -/
def ActualProtection : Selection.Outcome model domain original (normalized model domain reference) → Prop
  | .blocked rejected => ∀ program : Complete.FiniteProgram model.source.code,
      ¬ Complete.holds model domain original (normalized model domain reference) program
        (rejected (clip (horizon domain) program.2)).row
  | .selected choice => ∀ against : Opponent model.source.code,
      Synthesis.accepts model.source.code (economicAxes point.val.source point.val.cut)
        (actualEvaluation model point.val original choice.policy.protocol against)
        (actualEvaluation model point.val original reference.2 against)

theorem every_prepared_whole_word_protects_its_actual_original_window :
    ActualProtection point prepared.outcome := by
  cases prepared.outcome with
  | selected choice =>
      intro against
      have accepted := (Selection.acceptable_iff_every_common_external_opponent model domain original _ _).mp
        choice.policy.accepted point against
      have same := clipping_preserves_the_whole_table_evaluation model point.val original reference.2 domain point.property
        (Nat.le_refl _) (externalTable point.val against)
      rw [one_common_table_preserves_the_entire_actual_evaluation,one_common_table_preserves_the_entire_actual_evaluation] at same
      rw [same] at accepted
      exact accepted
  | blocked rejected =>
      intro program
      exact (Complete.normalized_row_iff model domain original (Nat.le_refl _) _ _ _).not.mp
        (rejected (clip (horizon domain) program.2)).broken

abbrev final := prepared.finish point rival
abbrev facade := Native.AuthorityRuntime.facade (prepared.bound point rival)
abbrev activated := Inquiry.Runtime.readState (prepared.bound point rival) (depth (final prepared point rival))
abbrev native := Inquiry.Runtime.read (prepared.bound point rival) (depth (final prepared point rival))

theorem the_same_actual_root_consumes_whole_word_selection_ledger_and_next :
    let current := activated prepared point rival
    Complete.Contract model domain original (normalized model domain reference) prepared.outcome ∧
      Selection.review model domain original (normalized model domain reference) prepared.outcome = true ∧
      ActualProtection point prepared.outcome ∧
      (∀ ordinal ≤ arrival point.val,Native.Coupling.Match model.source.code point.val.source.input
        (final prepared point rival).source.input (Financial.accountAt point.val.source.input ordinal)
        (Financial.accountAt (final prepared point rival).source.input ordinal)) ∧
      (native prepared point rival).joint.finance = Financial.accountAt (final prepared point rival).source.input
        (arrival (final prepared point rival)+1) ∧
      HEq ((facade prepared point rival).readoutAt current .responsibilities)
        (current.tick.generated.projectionOutcome (.component ())) ∧
      HEq current.tick.generated.wholeLedgerWriteBack
        (current.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current.current.visit.current) ∧
      current.tick.nextCurrent = (facade prepared point rival).process.stateAt
        ((facade prepared point rival).process.successor current.state) := by
  let current := activated prepared point rival
  have rooted := (facade prepared point rival).readoutAt_factorizes current .responsibilities
  refine ⟨Complete.every_generated_outcome_covers_all_finite_programs model domain original (Nat.le_refl _) _ _,
    Selection.every_generated_outcome_is_independently_reviewable model domain original _ _,
    every_prepared_whole_word_protects_its_actual_original_window prepared point,?_,?_,
    rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩
  · intro ordinal earlier
    unfold final Prepared.finish
    cases prepared.outcome with
    | selected choice =>
        exact Future.complete_finance_before point.val.source point.val.entry point.val.cut
          (controller point.val original choice.policy.protocol rival) (schedule point.val original choice.policy.protocol).val
          rfl ordinal earlier
    | blocked =>
        exact Native.Coupling.History.complete_accounts model.source.code point.val.source.input point.val.source.input
          rfl rfl ordinal (fun _ _ => rfl) point.val.source.body point.val.source.body rfl rfl ordinal (Nat.le_refl _)
  · rw [(native prepared point rival).joint_exact]
    have account := (Native.generate (final prepared point rival).source (depth (final prepared point rival))).finance_exact
    have address : depth (final prepared point rival)+2 = arrival (final prepared point rival)+1 := by
      dsimp only [depth,arrival]
      omega
    rw [address] at account
    exact account

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Runtime
