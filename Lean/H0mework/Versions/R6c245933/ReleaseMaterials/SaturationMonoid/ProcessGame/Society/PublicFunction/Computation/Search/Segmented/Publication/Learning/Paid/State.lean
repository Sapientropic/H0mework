import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Source

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

private def ruleDecidableEq : DecidableEq (Prefix.Rule code) := fun first second =>
  decidable_of_iff (∀ key : code.Key,
    first.work.val key (code.key_mem key) = second.work.val key (code.key_mem key) ∧
    (first.events key (code.key_mem key)).val = (second.events key (code.key_mem key)).val) (by
    constructor
    · intro same
      have work : first.work = second.work := Subtype.ext (funext fun key => funext fun _ => (same key).1)
      have events : first.events = second.events := funext fun key => funext fun _ => Subtype.ext (same key).2
      cases first; cases second; cases work; cases events; rfl
    · intro same; subst second; exact fun _ => ⟨rfl,rfl⟩)
local instance : DecidableEq (Prefix.Rule code) := ruleDecidableEq

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (original : Prefix.Rule model.source.code)
  (baseline : Program model.source.code (horizon domain)) (actualHorizon : Nat)

/-- The cache retains an evaluated complete plan. Resource requests may consume
only a next stage already present in that plan's full responsibility comparison. -/
structure State where
  past : List (Prefix.Rule model.source.code)
  programme : Program model.source.code (horizon domain)
  beliefs : List (View (code := model.source.code))
  within : past.length ≤ horizon domain
  actualWithin : past.length ≤ actualHorizon
  retained : programme.controls.take past.length = past
  above : Selection.acceptable model domain original baseline programme
  planner : Rolling.Receipt.Planner model := Rolling.Receipt.defaultPlanner model

namespace State
variable {model domain original baseline actualHorizon}
  (state : State model domain original baseline actualHorizon)

def Booked (rule : Prefix.Rule model.source.code) : Prop :=
  state.past.length+1 < actualHorizon ∧ state.past.length+1 < horizon domain ∧
    state.programme.controls.take (state.past.length+1) = state.past ++ [rule]

instance (rule : Prefix.Rule model.source.code) : Decidable (state.Booked rule) := by
  unfold Booked; infer_instance

def current (point : View (code := model.source.code)) (rival : Opponent model.source.code) :=
  Window.Observed.Transcript.actualView state.past point rival

theorem current_is_the_actual_control_prefix (point : View (code := model.source.code))
    (rival : Opponent model.source.code) :
    (state.current point rival).point = Splice.install point.point rival state.past := by
  have actual (controls : List (Prefix.Rule model.source.code)) (view : View (code := model.source.code)) :
      (Window.Observed.Transcript.actualView controls view rival).point = Splice.install view.point rival controls := by
    induction controls generalizing view with
    | nil => rfl
    | cons rule rest ih => exact ih (Evidence.after view rule rival)
  exact actual state.past point

def carry (rule : Prefix.Rule model.source.code) (booked : state.Booked rule) :
    State model domain original baseline actualHorizon where
  past := state.past ++ [rule]
  programme := state.programme
  beliefs := Window.Observed.Transcript.publicViews [rule] state.beliefs
  within := by
    have room := booked.2.1
    simp only [List.length_append,List.length_singleton]
    omega
  actualWithin := by
    have room := booked.1
    simp only [List.length_append,List.length_singleton]
    omega
  retained := by simpa only [List.length_append,List.length_singleton] using booked.2.2
  above := state.above
  planner := state.planner

theorem carrying_a_reserved_request_is_the_actual_next_stage
    (rule : Prefix.Rule model.source.code) (booked : state.Booked rule)
    (point : View (code := model.source.code)) (rival : Opponent model.source.code) :
    (state.carry rule booked).current point rival = Evidence.after (state.current point rival) rule rival := by
  change Window.Observed.Transcript.actualView (state.past ++ [rule]) point rival = _
  unfold Window.Observed.Transcript.actualView
  rw [List.foldl_append]
  rfl

abbrev tail := clip (horizon domain) (Splice.word (state.programme.controls.drop state.past.length))

/-- Only the paying reader changes its local policy; other sites retain the
cached policy. The reader prepares all own-inbox branches, not a private-world oracle. -/
def learned (reader : Fin model.source.code.sites) : Prefix.Rule model.source.code :=
  let fallback := state.programme.at original state.past.length
  let remaining := min (horizon domain) (horizon (state.beliefs.map View.point))
  let localRule := Rolling.Receipt.ruleWith model state.beliefs original (clip remaining state.tail) fallback state.planner
  {work := ⟨fun key inside => if key.1 = reader then localRule.work.val key inside else fallback.work.val key inside, by
      apply model.source.code.every_local_policy_is_enumerated
      intro key inside
      split
      · exact (List.mem_pi _ _).mp localRule.work.property key inside
      · exact (List.mem_pi _ _).mp fallback.work.property key inside⟩,
    events := fun key inside => if key.1 = reader then localRule.events key inside else fallback.events key inside}

abbrev proposal (reader : Fin model.source.code.sites) :=
  Prefix.extension (horizon domain) state.past
    (Splice.word (state.learned reader :: state.programme.controls.drop (state.past.length+1)))

inductive Decision (reader : Fin model.source.code.sites) where
  | admitted (accepted : Selection.acceptable model domain original state.programme (state.proposal reader))
  | refused (rejected : Selection.Rejection model domain original state.programme (state.proposal reader))

def inspect (reader : Fin model.source.code.sites) :
    state.Decision reader :=
  if accepted : Selection.acceptable model domain original state.programme (state.proposal reader) then
    .admitted accepted
  else
    match Distributed.inspect (Selection.holds model domain original state.programme (state.proposal reader))
        (Replanning.rows model domain) with
    | .accepted all => False.elim (accepted all)
    | .rejected row generated broken => .refused ⟨row,generated,broken⟩

theorem inspection_equals_the_original_complete_row_check (reader : Fin model.source.code.sites) :
    state.inspect reader =
      match Distributed.inspect (Selection.holds model domain original state.programme (state.proposal reader))
          (Replanning.rows model domain) with
      | .accepted all => .admitted all
      | .rejected row generated broken => .refused ⟨row,generated,broken⟩ := by
  unfold inspect
  split
  · rename_i accepted
    cases checked : Distributed.inspect (Selection.holds model domain original state.programme (state.proposal reader))
        (Replanning.rows model domain) with
    | accepted all => rfl
    | rejected row generated broken => exact False.elim (broken (accepted row generated))
  · rename_i rejected
    cases checked : Distributed.inspect (Selection.holds model domain original state.programme (state.proposal reader))
        (Replanning.rows model domain) with
    | accepted all => exact False.elim (rejected all)
    | rejected row generated broken => rfl

def commit (reader : Fin model.source.code.sites) (reading : Fin model.source.code.signals)
    (decision : state.Decision reader) :
    State model domain original baseline actualHorizon :=
  match decision with
  | .refused _ => {state with beliefs := fiber state.beliefs reader reading}
  | .admitted accepted =>
      {state with
        beliefs := fiber state.beliefs reader reading
        programme := state.proposal reader
        retained := Prefix.every_completion_preserves_the_committed_control_prefix _ _ _ state.within
        above := Selection.acceptable_trans model domain original _ _ _ accepted state.above}

def revise (reader : Fin model.source.code.sites) (reading : Fin model.source.code.signals) :=
  state.commit reader reading (state.inspect reader)

theorem revision_keeps_every_already_executed_request
    (reader : Fin model.source.code.sites) (reading : Fin model.source.code.signals) :
    (state.revise reader reading).past = state.past := by
  unfold revise commit; cases state.inspect reader <;> rfl

theorem committing_the_stored_decision_preserves_all_paid_past
    (reader : Fin model.source.code.sites) (reading : Fin model.source.code.signals)
    (decision : state.Decision reader) :
    (state.commit reader reading decision).past = state.past := by
  cases decision <;> rfl

theorem no_other_site_uses_the_paying_readers_local_search
    (reader site : Fin model.source.code.sites) (signal : Fin model.source.code.signals)
    (different : site ≠ reader) :
    (state.learned reader).work.val (site,signal) (model.source.code.key_mem _) =
      (state.programme.at original state.past.length).work.val (site,signal) (model.source.code.key_mem _) ∧
    (state.learned reader).events (site,signal) (model.source.code.key_mem _) =
      (state.programme.at original state.past.length).events (site,signal) (model.source.code.key_mem _) := by
  simp only [learned,if_neg different]
  exact ⟨trivial,trivial⟩

end State
end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid
