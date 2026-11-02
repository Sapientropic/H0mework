import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Review

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Runtime

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

def execute (point : Cursor code) (rule : Distributed.Recall.Information.Agency.Protocol.Rule code)
    (rival : Opponent code) : Cursor code :=
  let next := point.target rule rival
  ⟨next.reference,next.reference_generated,next.history,next.original,next.opponent,next.side,
    point.targetInput rule rival,next.feedbackOverrides,
    point.cut+Cut.horizon point.source point.entry point.cut,point.ownerStart⟩

theorem executes_the_whole_original_window (point : Cursor code)
    (rule : Distributed.Recall.Information.Agency.Protocol.Rule code) (rival : Opponent code) :
    seed (execute point rule rival) = Residual.run code
      (Residual.scheduleAt point.source point.cut (term point.source point.entry point.cut rule).val)
      ⟨Cursor.controller point rule rival,point.entry.budget⟩ (seed point)
      (Cut.horizon point.source point.entry point.cut) :=
  Future.the_whole_future_run_is_the_actual_state point.source point.entry point.cut
    (Cursor.controller point rule rival) (term point.source point.entry point.cut rule).val _

theorem the_full_execution_uses_exactly_the_original_remaining_budget (point : Cursor code)
    (rule : Distributed.Recall.Information.Agency.Protocol.Rule code) (rival : Opponent code) :
    (seed (execute point rule rival)).remaining = 0 := by
  rw [executes_the_whole_original_window,Residual.remaining_is_the_seed_budget]
  exact Nat.sub_self _

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem advance_preserves_a_historical_refusal (policy : Option code.Policy)
    (input : Input code) (state : State code) (refused : state.frame.localLegal = false) :
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

theorem the_complete_actual_window_never_clears_the_historical_refusal (point : Cursor code)
    (rule : Distributed.Recall.Information.Agency.Protocol.Rule code) (rival : Opponent code)
    (refused : (seed point).frame.localLegal = false) :
    (seed (execute point rule rival)).frame.localLegal = false := by
  rw [executes_the_whole_original_window]
  have invariant (count : Nat) : (Residual.run code
      (Residual.scheduleAt point.source point.cut (term point.source point.entry point.cut rule).val)
      ⟨Cursor.controller point rule rival,point.entry.budget⟩ (seed point) count).frame.localLegal = false := by
    induction count with
    | zero => exact refused
    | succ count ih => exact advance_preserves_a_historical_refusal _ _ _ ih
  exact invariant _

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (known : List (Cursor model.source.code)) (point : Cursor model.source.code)
  (reference : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)

abbrev domain := point::known
abbrev plan := Review.compile model (domain model known point) reference

structure Prepared where
  outcome : Search.Outcome model (domain model known point) reference
  original : outcome = plan model known point reference

def prepare : Prepared model known point reference := ⟨plan model known point reference,rfl⟩

namespace Prepared
variable {model known point reference}

def finish (prepared : Prepared model known point reference) (rival : Opponent model.source.code) : Cursor model.source.code :=
  match prepared.outcome with
  | .selected choice => execute point choice.policy.protocol rival
  | .blocked _ => point

def bound (prepared : Prepared model known point reference) (rival : Opponent model.source.code) :=
  Replanning.native model (prepared.finish rival)

end Prepared

variable (rival : Opponent model.source.code)

def finish : Cursor model.source.code := (prepare model known point reference).finish rival

theorem Prepared.is_the_original_generated_actual_execution
    (prepared : Prepared model known point reference) :
    prepared.finish rival = Runtime.finish model known point reference rival := by
  unfold Prepared.finish Runtime.finish prepare
  rw [prepared.original]
  rfl

def Protected : Search.Outcome model (domain model known point) reference → Prop
  | .blocked rejected =>
      ∀ rule : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code,
        ¬ Search.holds model (domain model known point) reference rule (rejected rule).row
  | .selected choice =>
      Review.verify model (domain model known point) reference choice.policy.protocol = true ∧
      (∀ against : Opponent model.source.code,
        Synthesis.accepts model.source.code (economicAxes point.source point.cut)
          (Window.evaluate model point choice.policy.protocol against) (Window.evaluate model point reference against)) ∧
      (∀ other : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code,
        Search.acceptable model (domain model known point) choice.policy.protocol other →
          ¬ Distributed.Improves (Search.axes model (domain model known point))
            (Search.benefit model (domain model known point)) choice.policy.protocol other) ∧
      ((∃ other : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code,
        Search.acceptable model (domain model known point) reference other ∧
          Distributed.Improves (Search.axes model (domain model known point))
            (Search.benefit model (domain model known point)) reference other) →
        Distributed.Improves (Search.axes model (domain model known point))
          (Search.benefit model (domain model known point)) reference choice.policy.protocol)

theorem the_generated_plan_is_independently_verified_and_protects_every_common_opponent :
    Protected model known point reference (plan model known point reference) := by
  cases plan model known point reference with
  | blocked rejected => exact fun rule => (rejected rule).broken
  | selected choice =>
      refine ⟨?_,?_,
        Search.selected_has_no_full_responsibility_dominator model _ reference choice,
        Search.every_full_responsibility_improvement_is_realized model _ reference choice⟩
      · rw [Review.verify_exact]
        exact Search.independently_replayed_choice_is_accepted model _ reference choice
      · intro against
        exact (Search.acceptable_iff_every_common_external_opponent model _ reference choice.policy.protocol).mp
          choice.policy.accepted ⟨point,List.mem_cons_self⟩ against

theorem the_actual_full_execution_keeps_the_complete_original_financial_prefix
    (ordinal : Nat) (earlier : ordinal ≤ arrival point) :
    Native.Coupling.Match model.source.code point.source.input (finish model known point reference rival).source.input
      (Financial.accountAt point.source.input ordinal)
      (Financial.accountAt (finish model known point reference rival).source.input ordinal) := by
  unfold finish Prepared.finish prepare
  dsimp only
  cases plan model known point reference with
  | selected choice =>
      exact Future.complete_finance_before point.source point.entry point.cut
        (Cursor.controller point choice.policy.protocol rival) (term point.source point.entry point.cut choice.policy.protocol).val
        rfl ordinal earlier
  | blocked rejected =>
      exact Native.Coupling.History.complete_accounts model.source.code point.source.input point.source.input
        rfl rfl ordinal (fun _ _ => rfl) point.source.body point.source.body rfl rfl ordinal (Nat.le_refl _)

abbrev bound := Replanning.native model (finish model known point reference rival)
abbrev facade := Native.AuthorityRuntime.facade (bound model known point reference rival)
abbrev activated := Inquiry.Runtime.readState (bound model known point reference rival)
  (depth (finish model known point reference rival))
abbrev native := Inquiry.Runtime.read (bound model known point reference rival)
  (depth (finish model known point reference rival))

theorem the_original_root_consumes_full_responsibility_selection_actual_execution_and_next :
    let current := activated model known point reference rival
    Protected model known point reference (plan model known point reference) ∧
      Search.review model (domain model known point) reference (plan model known point reference) = true ∧
      ((seed point).frame.localLegal = false →
        (seed (finish model known point reference rival)).frame.localLegal = false) ∧
      (∀ ordinal ≤ arrival point,Native.Coupling.Match model.source.code point.source.input
        (finish model known point reference rival).source.input (Financial.accountAt point.source.input ordinal)
        (Financial.accountAt (finish model known point reference rival).source.input ordinal)) ∧
      (native model known point reference rival).joint.finance =
        Financial.accountAt (finish model known point reference rival).source.input
          (arrival (finish model known point reference rival)+1) ∧
      HEq ((facade model known point reference rival).readoutAt current .responsibilities)
        (current.tick.generated.projectionOutcome (.component ())) ∧
      HEq current.tick.generated.wholeLedgerWriteBack
        (current.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current.current.visit.current) ∧
      current.tick.nextCurrent = (facade model known point reference rival).process.stateAt
        ((facade model known point reference rival).process.successor current.state) := by
  let current := activated model known point reference rival
  have rooted := (facade model known point reference rival).readoutAt_factorizes current .responsibilities
  refine ⟨the_generated_plan_is_independently_verified_and_protects_every_common_opponent model known point reference,
    Search.every_generated_outcome_is_independently_reviewable model _ reference _,
    ?_,
    the_actual_full_execution_keeps_the_complete_original_financial_prefix model known point reference rival,
    ?_,rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩
  · intro refused
    unfold finish Prepared.finish prepare
    dsimp only
    cases plan model known point reference with
    | blocked => exact refused
    | selected choice => exact the_complete_actual_window_never_clears_the_historical_refusal point _ rival refused
  · rw [(native model known point reference rival).joint_exact]
    have account := (Native.generate (finish model known point reference rival).source
      (depth (finish model known point reference rival))).finance_exact
    have address : depth (finish model known point reference rival)+2 =
        arrival (finish model known point reference rival)+1 := by dsimp only [depth,arrival];omega
    rw [address] at account
    exact account

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Runtime
