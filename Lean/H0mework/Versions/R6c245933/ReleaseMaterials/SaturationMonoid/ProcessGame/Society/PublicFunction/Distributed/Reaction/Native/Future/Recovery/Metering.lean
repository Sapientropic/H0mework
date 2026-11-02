import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Source.Cursor
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Search.Billing

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {old : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {oldDepth : Nat} {word : List (Action old)}

namespace Cursor
variable (cursor : Recovery.Cursor old oldDepth word)

/-- A fee extends the actual input without consuming an original task position. -/
abbrev append (emitted : List (Action old)) : Recovery.Cursor old oldDepth word :=
  cursor.appendActual emitted

theorem submitted (emitted : List (Action old)) :
    ((append cursor emitted).source.val.actualExecution cursor.depth).submitted = emitted :=
  Machine.Continuation.submitted cursor.source.val cursor.count emitted

theorem before (emitted : List (Action old)) :
    ((append cursor emitted).source.val.actualExecution cursor.depth).before = cursor.before :=
  Machine.Continuation.before cursor.source.val cursor.count emitted

theorem next (emitted : List (Action old)) :
    (append cursor emitted).before = cursor.source.val.code.law.next cursor.before emitted := by
  exact Machine.Continuation.actual_next cursor.source.val cursor.count emitted

theorem prior_events (emitted : List (Action old)) (ordinal : Nat) (earlier : ordinal < cursor.depth+1) :
    ProgrammeSource.rawEvent (append cursor emitted).source.val.input
      (ProgrammeHistory.visitAt cursor.source.val.input ordinal).current =
    ProgrammeSource.rawEvent cursor.source.val.input (ProgrammeHistory.visitAt cursor.source.val.input ordinal).current :=
  Machine.Continuation.prior_events cursor.source.val cursor.count emitted ordinal earlier

theorem prior_currents (emitted : List (Action old)) (ordinal : Nat) (earlier : ordinal ≤ cursor.depth+1) :
    (ProgrammeHistory.visitAt (append cursor emitted).source.val.input ordinal).current =
      (ProgrammeHistory.visitAt cursor.source.val.input ordinal).current :=
  Machine.Continuation.prior_currents cursor.source.val cursor.count emitted ordinal earlier

theorem financial_prefix (emitted : List (Action old)) (ordinal : Nat) (earlier : ordinal ≤ cursor.depth+1) :
    Coupling.Match cursor.source.val.code cursor.source.val.input (append cursor emitted).source.val.input
      (Financial.accountAt cursor.source.val.input ordinal)
      (Financial.accountAt (append cursor emitted).source.val.input ordinal) :=
  Machine.Continuation.complete_financial_prefix cursor.source.val cursor.count emitted ordinal earlier
end Cursor

variable (cursor : Recovery.Cursor old oldDepth word) (actor : Party)

/-- Resource-consuming quotes are taken from this source's registered own actions.
The use is external to the original public task, so it cannot discharge a task slot. -/
def IsFee (request : Action old) : Prop :=
  request.signer = actor ∧ (∀ consent ∈ request.consents,consent = actor) ∧
  ¬ Mandate.TaskUse old.scope request ∧
  match request.operation with
  | .use bearer bundle .external => bearer = actor ∧
      NonnegativeBundle Good bundle ∧ ∃ good ∈ cursor.source.val.code.goods,0 < amount Good bundle good
  | _ => False

instance (request : Action old) : Decidable (IsFee cursor actor request) := by
  unfold IsFee
  cases request.operation <;> try infer_instance
  rename_i bearer bundle purpose
  cases purpose <;> infer_instance

def quote (tariffPosition : Nat) : Option (Action old) :=
  match cursor.source.val.code.actions[tariffPosition]? with
  | none => none
  | some fee => if IsFee cursor actor fee then some fee else none

theorem quote_is_original_personal_and_nonzero (tariffPosition : Nat) (fee : Action old)
    (found : quote cursor actor tariffPosition = some fee) :
    fee ∈ cursor.source.val.code.actions ∧ IsFee cursor actor fee := by
  unfold quote at found
  split at found
  · cases found
  · rename_i request registered
    split at found
    next suitable =>
      cases Option.some.inj found
      exact ⟨List.mem_of_getElem? registered,suitable⟩
    next => cases found

variable (fee : Action old) (units : Nat)
abbrev invoice := List.replicate units fee
abbrev attempt := Mandate.Replay.compile old.base old.scope cursor.before (invoice fee units)
abbrev charged := Cursor.append cursor (attempt cursor fee units).output

theorem the_invoice_is_really_attempted_at_this_actual_cut :
    ((charged cursor fee units).source.val.actualExecution cursor.depth).submitted = (attempt cursor fee units).output ∧
    ((charged cursor fee units).source.val.actualExecution cursor.depth).before = cursor.before :=
  ⟨Cursor.submitted _ _,Cursor.before _ _⟩

theorem a_refused_invoice_has_its_exact_actual_financial_or_permission_obstruction
    (refused : (attempt cursor fee units).succeeded = false) :
    ∃ item ∈ (charged cursor fee units).source.val.code.law.rawItems
        ((charged cursor fee units).source.val.actualExecution cursor.depth).before
        ((charged cursor fee units).source.val.actualExecution cursor.depth).submitted,
      item.index = (attempt cursor fee units).consumed.length ∧
        ¬ (charged cursor fee units).source.val.code.law.Valid item.before item.request := by
  rw [(the_invoice_is_really_attempted_at_this_actual_cut cursor fee units).1,
    (the_invoice_is_really_attempted_at_this_actual_cut cursor fee units).2]
  change ∃ item ∈ cursor.source.val.code.law.rawItems cursor.before (attempt cursor fee units).output,
    item.index = _ ∧ ¬ cursor.source.val.code.law.Valid item.before item.request
  rw [cursor.source.property.1]
  exact (attempt cursor fee units).failure_is_an_actual_raw_item refused

variable {cursor actor fee units}

/-- Construction/metering is one registered service unit. Comparison reserves
one request-interpreter visit per potential check (including the baseline),
three preparation passes, and one selection comparison per catalogue entry. -/
abbrev comparisonUnits (pending : List (Action old)) (catalogue : List (List (Action old))) : Nat :=
  Search.Billing.comparisonUnits pending catalogue

abbrev Ranked (stage : Recovery.Cursor old oldDepth word) :=
  Search.Billing.Ranked (Search.Context.ofBound stage.model) stage.before stage.residual
abbrev rank (stage : Recovery.Cursor old oldDepth word) :=
  Search.Billing.rank (Search.Context.ofBound stage.model) stage.before stage.residual
abbrev prefer {stage : Recovery.Cursor old oldDepth word} (left right : Ranked stage) :=
  Search.Billing.prefer left right
abbrev choose (stage : Recovery.Cursor old oldDepth word) :=
  Search.Billing.choose (Search.Context.ofBound stage.model) stage.before stage.residual

theorem chosen_is_baseline_or_registered (stage : Recovery.Cursor old oldDepth word)
    (catalogue : List (List (Action old))) :
    (choose stage catalogue).preparation = [] ∨ (choose stage catalogue).preparation ∈ catalogue :=
  Search.Billing.chosen_is_baseline_or_registered _ _ _ _

theorem chosen_maximal (stage : Recovery.Cursor old oldDepth word)
    (catalogue : List (List (Action old))) (preparation : List (Action old)) (inside : preparation ∈ catalogue) :
    (rank stage preparation).value ≤ (choose stage catalogue).quality (Search.Context.ofBound stage.model) stage.before stage.residual :=
  Search.Billing.chosen_maximal _ _ _ _ _ inside

theorem chosen_preparation_is_legal (stage : Recovery.Cursor old oldDepth word)
    (catalogue : List (List (Action old))) :
    ((choose stage catalogue).prepared (Search.Context.ofBound stage.model) stage.before).succeeded = true :=
  Search.Billing.chosen_preparation_is_legal _ _ _ _

abbrev requestVisits (stage : Recovery.Cursor old oldDepth word) :=
  Search.Billing.requestVisits (Search.Context.ofBound stage.model) stage.before stage.residual

theorem every_evaluated_request_visit_is_reserved (stage : Recovery.Cursor old oldDepth word)
    (catalogue : List (List (Action old))) :
    requestVisits stage [] + (catalogue.map (requestVisits stage)).sum + catalogue.length <
      comparisonUnits stage.residual catalogue :=
  Search.Billing.every_evaluated_request_visit_is_reserved _ _ _ _

def restored (stage : Recovery.Cursor old oldDepth word) (catalogue : List (List (Action old))) :
    Recovery.Cursor old oldDepth word := stage.replayPreparation (choose stage catalogue).preparation

structure Prefix (first last : Recovery.Cursor old oldDepth word) : Prop where
  code : last.source.val.code = first.source.val.code
  depth : first.depth ≤ last.depth
  events : ∀ ordinal, ordinal < first.depth+1 →
    ProgrammeSource.rawEvent last.source.val.input (ProgrammeHistory.visitAt first.source.val.input ordinal).current =
      ProgrammeSource.rawEvent first.source.val.input (ProgrammeHistory.visitAt first.source.val.input ordinal).current
  currents : ∀ ordinal, ordinal ≤ first.depth+1 →
    (ProgrammeHistory.visitAt last.source.val.input ordinal).current =
      (ProgrammeHistory.visitAt first.source.val.input ordinal).current

namespace Prefix
theorem refl (first : Recovery.Cursor old oldDepth word) : Prefix first first :=
  ⟨rfl,Nat.le_refl _,fun _ _ => rfl,fun _ _ => rfl⟩

theorem trans {first middle last : Recovery.Cursor old oldDepth word}
    (left : Prefix first middle) (right : Prefix middle last) : Prefix first last := by
  have ordered := left.depth
  refine ⟨right.code.trans left.code,left.depth.trans right.depth,?_,?_⟩
  · intro ordinal earlier
    have later := right.events ordinal (by omega)
    rw [left.currents ordinal (by omega)] at later
    exact later.trans (left.events ordinal earlier)
  · intro ordinal earlier
    exact (right.currents ordinal (by omega)).trans (left.currents ordinal earlier)

theorem append (first : Recovery.Cursor old oldDepth word) (emitted : List (Action old)) :
    Prefix first (Cursor.append first emitted) :=
  ⟨rfl,Nat.le_succ _,Cursor.prior_events first emitted,Cursor.prior_currents first emitted⟩

theorem replay (first : Recovery.Cursor old oldDepth word) (preparation : List (Action old)) :
    Prefix first (first.replayPreparation preparation) :=
  ⟨rfl,Nat.le_succ _,Machine.Continuation.prior_events first.source.val first.count _,
    Machine.Continuation.prior_currents first.source.val first.count _⟩
end Prefix

inductive Result (cursor : Recovery.Cursor old oldDepth word) (tariffPosition : Nat) where
  | finished (empty : cursor.residual = [])
  | unpriced (head : Action old) (tail : List (Action old)) (pending : cursor.residual = head::tail)
      (absent : quote cursor head.signer tariffPosition = none)
  | constructionRefused (head : Action old) (tail : List (Action old)) (pending : cursor.residual = head::tail)
      (fee : Action old) (registered : quote cursor head.signer tariffPosition = some fee)
      (refused : (attempt cursor fee 1).succeeded = false)
  | comparisonRefused (head : Action old) (tail : List (Action old)) (pending : cursor.residual = head::tail)
      (fee : Action old) (registered : quote cursor head.signer tariffPosition = some fee)
      (constructionPaid : (attempt cursor fee 1).succeeded = true)
      (refused : (attempt (charged cursor fee 1) fee
        (comparisonUnits cursor.residual (Search.catalogue (charged cursor fee 1).model
          (charged cursor fee 1).before head.signer cursor.residual))).succeeded = false)
  | searched (head : Action old) (tail : List (Action old)) (pending : cursor.residual = head::tail)
      (fee : Action old) (registered : quote cursor head.signer tariffPosition = some fee)
      (constructionPaid : (attempt cursor fee 1).succeeded = true)
      (comparisonPaid : (attempt (charged cursor fee 1) fee
        (comparisonUnits cursor.residual (Search.catalogue (charged cursor fee 1).model
          (charged cursor fee 1).before head.signer cursor.residual))).succeeded = true)

/-- The tariff position selects a registered source action, not a payment proof. Both payment decisions are
generated before the catalogue's quality fold is released. -/
def run (cursor : Recovery.Cursor old oldDepth word) (tariffPosition : Nat) : Result cursor tariffPosition :=
  match pending : cursor.residual with
  | [] => .finished pending
  | head::tail => match registered : quote cursor head.signer tariffPosition with
    | none => .unpriced head tail pending registered
    | some fee =>
      if paid : (attempt cursor fee 1).succeeded = true then
        let built := charged cursor fee 1
        let catalogue := Search.catalogue built.model built.before head.signer cursor.residual
        if compared : (attempt built fee (comparisonUnits cursor.residual catalogue)).succeeded = true then
          .searched head tail pending fee registered paid compared
        else .comparisonRefused head tail pending fee registered paid (Bool.eq_false_iff.mpr compared)
      else .constructionRefused head tail pending fee registered (Bool.eq_false_iff.mpr paid)

namespace Result
variable {cursor : Recovery.Cursor old oldDepth word} {tariffPosition : Nat}

def finish : Result cursor tariffPosition → Recovery.Cursor old oldDepth word
  | .finished _ | .unpriced .. => cursor
  | .constructionRefused _ _ _ fee _ _ => charged cursor fee 1
  | .comparisonRefused head _ _ fee _ _ _ =>
      let built := charged cursor fee 1
      charged built fee (comparisonUnits cursor.residual (Search.catalogue built.model built.before head.signer cursor.residual))
  | .searched head _ _ fee _ _ _ =>
      let built := charged cursor fee 1
      let catalogue := Search.catalogue built.model built.before head.signer cursor.residual
      restored (charged built fee (comparisonUnits cursor.residual catalogue)) catalogue

theorem original_positions_survive (made : Result cursor tariffPosition) : made.finish.consumed ++ made.finish.residual = word :=
  made.finish.split

theorem preserves (made : Result cursor tariffPosition) : Prefix cursor made.finish := by
  cases made with
  | finished _ => exact Prefix.refl _
  | unpriced => exact Prefix.refl _
  | constructionRefused _ _ _ fee _ _ => exact Prefix.append _ _
  | comparisonRefused head _ _ fee _ _ _ => exact (Prefix.append _ _).trans (Prefix.append _ _)
  | searched head _ _ fee _ _ _ =>
      exact ((Prefix.append _ _).trans (Prefix.append _ _)).trans (Prefix.replay _ _)

theorem complete_financial_prefix (made : Result cursor tariffPosition) (ordinal : Nat)
    (earlier : ordinal ≤ cursor.depth+1) :
    Coupling.Match cursor.source.val.code cursor.source.val.input made.finish.source.val.input
      (Financial.accountAt cursor.source.val.input ordinal)
      (Financial.accountAt made.finish.source.val.input ordinal) := by
  apply Coupling.History.complete_accounts cursor.source.val.code cursor.source.val.input made.finish.source.val.input
    (congrArg Code.law made.preserves.code) (congrArg Code.initial made.preserves.code)
    (cursor.depth+1) made.preserves.events cursor.source.val.body made.finish.source.val.body rfl rfl ordinal earlier

def Released : Result cursor tariffPosition → Prop
  | .searched .. => True
  | _ => False

theorem every_released_search_has_two_actual_prior_payments (made : Result cursor tariffPosition) (released : made.Released) :
    ∃ head tail fee, cursor.residual = head::tail ∧ quote cursor head.signer tariffPosition = some fee ∧
      (attempt cursor fee 1).succeeded = true ∧
      (attempt (charged cursor fee 1) fee (comparisonUnits cursor.residual
        (Search.catalogue (charged cursor fee 1).model (charged cursor fee 1).before head.signer cursor.residual))).succeeded = true := by
  cases made <;> try cases released
  next head tail pending fee registered paid compared => exact ⟨head,tail,fee,pending,registered,paid,compared⟩

theorem no_original_position_is_credited_for_paying_or_refusing_a_bill (made : Result cursor tariffPosition)
    (unreleased : ¬ made.Released) : made.finish.consumed = cursor.consumed ∧ made.finish.residual = cursor.residual := by
  cases made <;> try exact ⟨rfl,rfl⟩
  exact False.elim (unreleased trivial)

def searches : Result cursor tariffPosition → Nat
  | .searched .. => 1
  | _ => 0

def rows : Result cursor tariffPosition → Nat
  | .searched head _ _ fee _ _ _ =>
      let built := charged cursor fee 1
      (Search.catalogue built.model built.before head.signer cursor.residual).length
  | _ => 0

def FundingFailed : Result cursor tariffPosition → Prop
  | .unpriced .. | .constructionRefused .. | .comparisonRefused .. => True
  | _ => False

instance (made : Result cursor tariffPosition) : Decidable made.FundingFailed := by
  cases made <;> unfold FundingFailed <;> infer_instance

/-- A stopped paid search exposes its own complete post-invoice catalogue. -/
def Quiescent : Result cursor tariffPosition → Prop
  | .finished _ => cursor.residual = []
  | .unpriced head _ _ _ => quote cursor head.signer tariffPosition = none
  | .constructionRefused _ _ _ fee _ _ => (attempt cursor fee 1).succeeded = false
  | .comparisonRefused head _ _ fee _ _ _ =>
      let built := charged cursor fee 1
      (attempt built fee (comparisonUnits cursor.residual
        (Search.catalogue built.model built.before head.signer cursor.residual))).succeeded = false
  | .searched head _ _ fee _ _ _ =>
      let built := charged cursor fee 1
      let catalogue := Search.catalogue built.model built.before head.signer cursor.residual
      let staged := charged built fee (comparisonUnits cursor.residual catalogue)
      ∀ preparation ∈ catalogue, (rank staged preparation).value = 0

theorem quiescent_of_no_progress (made : Result cursor tariffPosition)
    (stopped : ¬ made.finish.residual.length < cursor.residual.length) : made.Quiescent := by
  cases made with
  | finished empty => exact empty
  | unpriced _ _ _ absent => exact absent
  | constructionRefused _ _ _ _ _ refused => exact refused
  | comparisonRefused _ _ _ _ _ _ refused => exact refused
  | searched head tail pending fee registered constructionPaid comparisonPaid =>
      let built := charged cursor fee 1
      let catalogue := Search.catalogue built.model built.before head.signer cursor.residual
      let staged := charged built fee (comparisonUnits cursor.residual catalogue)
      have split := congrArg List.length
        ((choose staged catalogue).retry staged.model staged.before staged.residual).original_split
      simp only [List.length_append] at split
      change ¬ ((choose staged catalogue).retry staged.model staged.before staged.residual).residual.length <
        staged.residual.length at stopped
      have zero : ((choose staged catalogue).retry staged.model staged.before staged.residual).consumed.length = 0 := by omega
      have quality : (choose staged catalogue).quality staged.model staged.before staged.residual = 0 := by
        simp only [Search.Proposal.quality,chosen_preparation_is_legal,if_true,zero]
      intro preparation inside
      have bound := chosen_maximal staged catalogue preparation inside
      rw [quality] at bound
      exact Nat.eq_zero_of_le_zero bound

theorem progress_requires_a_released_search (made : Result cursor tariffPosition)
    (progress : made.finish.residual.length < cursor.residual.length) : made.Released := by
  by_contra unreleased
  have same := (made.no_original_position_is_credited_for_paying_or_refusing_a_bill unreleased).2
  rw [same] at progress
  exact (Nat.lt_irrefl _) progress

end Result

/-- The generated endpoint is cached with the result: recursive progress testing and
root readback do not rerun the paid quality fold. -/
structure Stage (cursor : Recovery.Cursor old oldDepth word) (position : Nat) where
  private mk ::
  result : Result cursor position
  generated : result = run cursor position
  endpoint : Recovery.Cursor old oldDepth word
  exact : endpoint = result.finish

def stage (cursor : Recovery.Cursor old oldDepth word) (position : Nat) : Stage cursor position :=
  let result := run cursor position
  let endpoint := result.finish
  ⟨result,rfl,endpoint,rfl⟩

namespace Stage
variable {cursor : Recovery.Cursor old oldDepth word} {position : Nat} (made : Stage cursor position)
theorem preserves : Prefix cursor made.endpoint := made.exact ▸ made.result.preserves

theorem quiescent (stopped : ¬ made.endpoint.residual.length < cursor.residual.length) :
    made.result.Quiescent := made.result.quiescent_of_no_progress (made.exact ▸ stopped)

theorem released (progress : made.endpoint.residual.length < cursor.residual.length) :
    made.result.Released := made.result.progress_requires_a_released_search (made.exact ▸ progress)
end Stage
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering
