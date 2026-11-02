import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Observation

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Observed

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
  (reference : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)

abbrev domain := views.map View.point
abbrev plan := Review.compile model (domain model views) reference

/-- Planning has no actual-world, past-opponent, or future-opponent argument. -/
structure Prepared where
  outcome : Search.Outcome model (domain model views) reference
  original : outcome = plan model views reference

def prepare : Prepared model views reference := ⟨plan model views reference,rfl⟩

variable (actual : View (code := model.source.code)) (rival : Opponent model.source.code)

namespace Prepared
variable {model views reference}

def finish (prepared : Prepared model views reference) : Cursor model.source.code :=
  match prepared.outcome with
  | .selected choice => Window.Runtime.execute actual.point choice.policy.protocol rival
  | .blocked _ => actual.point

def bound (prepared : Prepared model views reference) := Replanning.native model (prepared.finish actual rival)

def finalView (prepared : Prepared model views reference) : View (code := model.source.code) :=
  match prepared.outcome with
  | .selected choice => Observation.afterWindow actual choice.policy.protocol rival
  | .blocked _ => actual

def finalViews (prepared : Prepared model views reference) : List (View (code := model.source.code)) :=
  match prepared.outcome with
  | .selected choice => Observation.nextWindow choice.policy.protocol views
  | .blocked _ => views

theorem final_point_is_the_actual_execution (prepared : Prepared model views reference) :
    (prepared.finalView actual rival).point = prepared.finish actual rival := by
  unfold finalView finish
  cases prepared.outcome <;> rfl

theorem final_keeps_the_actual_original_debt_knowledge (prepared : Prepared model views reference)
    (covered : Knowledge.Contains views actual) :
    Knowledge.Contains prepared.finalViews (prepared.finalView actual rival) := by
  unfold finalViews finalView
  cases prepared.outcome with
  | blocked => exact covered
  | selected choice =>
      exact Observation.the_complete_public_successor_retains_every_actual_debt_origin
        views actual covered choice.policy.protocol rival

end Prepared

def finish := (prepare model views reference).finish actual rival

theorem Prepared.recognizes_the_original_generated_execution (prepared : Prepared model views reference) :
    prepared.finish actual rival = Observed.finish model views reference actual rival := by
  unfold Prepared.finish Observed.finish prepare
  rw [prepared.original]
  rfl

variable {actual rival}

def Protected : Search.Outcome model (domain model views) reference → Prop
  | .blocked rejected => ∀ rule : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code,
      ¬ Search.holds model (domain model views) reference rule (rejected rule).row
  | .selected choice => Review.verify model (domain model views) reference choice.policy.protocol = true ∧
      (∀ other : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code,
        Search.acceptable model (domain model views) choice.policy.protocol other →
          ¬ Distributed.Improves (Search.axes model (domain model views)) (Search.benefit model (domain model views))
            choice.policy.protocol other) ∧
      ((∃ other : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code,
        Search.acceptable model (domain model views) reference other ∧
          Distributed.Improves (Search.axes model (domain model views)) (Search.benefit model (domain model views))
            reference other) →
        Distributed.Improves (Search.axes model (domain model views)) (Search.benefit model (domain model views))
          reference choice.policy.protocol)

def AcceptedOn (actual : View (code := model.source.code)) :
    Search.Outcome model (domain model views) reference → Prop
  | .blocked _ => True
  | .selected choice => ∀ rival : Opponent model.source.code,
      Synthesis.accepts model.source.code (economicAxes actual.point.source actual.point.cut)
        (Window.evaluate model actual.point choice.policy.protocol rival)
        (Window.evaluate model actual.point reference rival)

theorem the_public_plan_is_verified_nondominated_and_realizes_every_available_tensor_improvement :
    Protected model views reference (plan model views reference) := by
  cases plan model views reference with
  | blocked rejected => exact fun rule => (rejected rule).broken
  | selected choice =>
      refine ⟨?_,Search.selected_has_no_full_responsibility_dominator model _ reference choice,
        Search.every_full_responsibility_improvement_is_realized model _ reference choice⟩
      rw [Review.verify_exact]
      exact Search.independently_replayed_choice_is_accepted model _ reference choice

theorem every_covered_actual_world_is_protected_by_the_same_public_plan
    (covered : Knowledge.Contains views actual) : AcceptedOn model views reference actual (plan model views reference) := by
  cases plan model views reference with
  | blocked => trivial
  | selected choice =>
      intro rival
      exact Observation.public_domain_acceptance_protects_the_actual_source model actual.point
        choice.policy.protocol rival (domain model views)
        (Knowledge.cursor_covered views actual covered) reference choice.policy.accepted

variable (actual rival)

theorem the_actual_execution_keeps_every_original_financial_prefix
    (ordinal : Nat) (earlier : ordinal ≤ arrival actual.point) :
    Native.Coupling.Match model.source.code actual.point.source.input
      (finish model views reference actual rival).source.input (Financial.accountAt actual.point.source.input ordinal)
      (Financial.accountAt (finish model views reference actual rival).source.input ordinal) := by
  unfold finish Prepared.finish prepare
  dsimp only
  cases plan model views reference with
  | selected choice =>
      exact Future.complete_finance_before actual.point.source actual.point.entry actual.point.cut
        (Cursor.controller actual.point choice.policy.protocol rival)
        (term actual.point.source actual.point.entry actual.point.cut choice.policy.protocol).val rfl ordinal earlier
  | blocked =>
      exact Native.Coupling.History.complete_accounts model.source.code actual.point.source.input actual.point.source.input
        rfl rfl ordinal (fun _ _ => rfl) actual.point.source.body actual.point.source.body rfl rfl ordinal (Nat.le_refl _)

abbrev bound := Replanning.native model (finish model views reference actual rival)
abbrev facade := Native.AuthorityRuntime.facade (bound model views reference actual rival)
abbrev activated := Inquiry.Runtime.readState (bound model views reference actual rival)
  (depth (finish model views reference actual rival))
abbrev native := Inquiry.Runtime.read (bound model views reference actual rival)
  (depth (finish model views reference actual rival))

theorem the_original_root_consumes_public_selection_actual_execution_full_finance_and_next
    (covered : Knowledge.Contains views actual) :
    let current := activated model views reference actual rival
    Protected model views reference (plan model views reference) ∧
      AcceptedOn model views reference actual (plan model views reference) ∧
      Search.review model (domain model views) reference (plan model views reference) = true ∧
      Knowledge.Contains (prepare model views reference).finalViews
        ((prepare model views reference).finalView actual rival) ∧
      ((seed actual.point).frame.localLegal = false →
        (seed (finish model views reference actual rival)).frame.localLegal = false) ∧
      (∀ ordinal ≤ arrival actual.point,Native.Coupling.Match model.source.code actual.point.source.input
        (finish model views reference actual rival).source.input (Financial.accountAt actual.point.source.input ordinal)
        (Financial.accountAt (finish model views reference actual rival).source.input ordinal)) ∧
      (native model views reference actual rival).joint.finance =
        Financial.accountAt (finish model views reference actual rival).source.input
          (arrival (finish model views reference actual rival)+1) ∧
      HEq ((facade model views reference actual rival).readoutAt current .responsibilities)
        (current.tick.generated.projectionOutcome (.component ())) ∧
      HEq current.tick.generated.wholeLedgerWriteBack
        (current.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current.current.visit.current) ∧
      current.tick.nextCurrent = (facade model views reference actual rival).process.stateAt
        ((facade model views reference actual rival).process.successor current.state) := by
  let current := activated model views reference actual rival
  have rooted := (facade model views reference actual rival).readoutAt_factorizes current .responsibilities
  refine ⟨the_public_plan_is_verified_nondominated_and_realizes_every_available_tensor_improvement model views reference,
    every_covered_actual_world_is_protected_by_the_same_public_plan model views reference covered,
    Search.every_generated_outcome_is_independently_reviewable model _ reference _,
    (prepare model views reference).final_keeps_the_actual_original_debt_knowledge actual rival covered,?_,
    the_actual_execution_keeps_every_original_financial_prefix model views reference actual rival,
    ?_,rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩
  · intro refused
    unfold finish Prepared.finish prepare
    dsimp only
    cases plan model views reference with
    | blocked => exact refused
    | selected choice =>
        exact Window.Runtime.the_complete_actual_window_never_clears_the_historical_refusal
          actual.point choice.policy.protocol rival refused
  · rw [(native model views reference actual rival).joint_exact]
    have account := (Native.generate (finish model views reference actual rival).source
      (depth (finish model views reference actual rival))).finance_exact
    have address : depth (finish model views reference actual rival)+2 =
        arrival (finish model views reference actual rival)+1 := by dsimp only [depth,arrival];omega
    rw [address] at account
    exact account

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Observed
