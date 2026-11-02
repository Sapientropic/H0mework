import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.Selection.Stage
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.Selection.Catalogue

import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Replay.Program.Session
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


structure Prefix (first last : Recovery.Cursor old oldDepth word) : Prop where
  code : last.source.val.code = first.source.val.code
  depth : first.depth ≤ last.depth
  pending : last.pending = first.pending
  events : ∀ ordinal, ordinal < first.depth+1 →
    ProgrammeSource.rawEvent last.source.val.input (ProgrammeHistory.visitAt first.source.val.input ordinal).current =
      ProgrammeSource.rawEvent first.source.val.input (ProgrammeHistory.visitAt first.source.val.input ordinal).current
  currents : ∀ ordinal, ordinal ≤ first.depth+1 →
    (ProgrammeHistory.visitAt last.source.val.input ordinal).current =
      (ProgrammeHistory.visitAt first.source.val.input ordinal).current

namespace Prefix
theorem refl (first : Recovery.Cursor old oldDepth word) : Prefix first first :=
  ⟨rfl,Nat.le_refl _,rfl,fun _ _ => rfl,fun _ _ => rfl⟩

theorem trans {first middle last : Recovery.Cursor old oldDepth word}
    (left : Prefix first middle) (right : Prefix middle last) : Prefix first last := by
  have ordered := left.depth
  refine ⟨right.code.trans left.code,left.depth.trans right.depth,right.pending.trans left.pending,?_,?_⟩
  · intro ordinal earlier
    have later := right.events ordinal (by omega)
    rw [left.currents ordinal (by omega)] at later
    exact later.trans (left.events ordinal earlier)
  · intro ordinal earlier
    exact (right.currents ordinal (by omega)).trans (left.currents ordinal earlier)

theorem append (first : Recovery.Cursor old oldDepth word) (emitted : List (Action old)) :
    Prefix first (Cursor.append first emitted) :=
  ⟨rfl,Nat.le_succ _,first.appendActual_pending emitted,Cursor.prior_events first emitted,Cursor.prior_currents first emitted⟩

theorem replay (first : Recovery.Cursor old oldDepth word) (preparation : List (Action old)) :
    Prefix first (first.replayPreparation preparation) :=
  ⟨rfl,Nat.le_succ _,first.replayPreparation_pending preparation,Machine.Continuation.prior_events first.source.val first.count _,
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
        (comparisonUnits cursor.residual (Search.repairs (charged cursor fee 1).model
          (charged cursor fee 1).before head.signer cursor.residual))).succeeded = false)
  | searched (head : Action old) (tail : List (Action old)) (pending : cursor.residual = head::tail)
      (fee : Action old) (registered : quote cursor head.signer tariffPosition = some fee)
      (constructionPaid : (attempt cursor fee 1).succeeded = true)
      (comparisonPaid : (attempt (charged cursor fee 1) fee
        (comparisonUnits cursor.residual (Search.repairs (charged cursor fee 1).model
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
        let catalogue := Search.repairs built.model built.before head.signer cursor.residual
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
      charged built fee (comparisonUnits cursor.residual (Search.repairs built.model built.before head.signer cursor.residual))
  | .searched head _ _ fee _ _ _ =>
      let built := charged cursor fee 1
      let catalogue := Search.repairs built.model built.before head.signer cursor.residual
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
        (Search.repairs (charged cursor fee 1).model (charged cursor fee 1).before head.signer cursor.residual))).succeeded = true := by
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
      (Search.repairs built.model built.before head.signer cursor.residual).length
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
        (Search.repairs built.model built.before head.signer cursor.residual))).succeeded = false
  | .searched head _ _ fee _ _ _ =>
      let built := charged cursor fee 1
      let catalogue := Search.repairs built.model built.before head.signer cursor.residual
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
      let catalogue := Search.repairs built.model built.before head.signer cursor.residual
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

theorem canonical (made : Result cursor tariffPosition) : made = run cursor tariffPosition := by
  cases made with
  | finished empty =>
    unfold run
    split
    · rfl
    · rename_i head tail pending
      have impossible := empty.symm.trans pending;cases impossible
  | unpriced head tail pending absent =>
    unfold run
    split
    · rename_i empty
      have impossible := empty.symm.trans pending;cases impossible
    · rename_i h t same
      rcases List.cons.inj (pending.symm.trans same) with ⟨rfl,rfl⟩
      split
      · rfl
      · rename_i fee registered
        rw [absent] at registered;cases registered
  | constructionRefused head tail pending fee registered refused =>
    unfold run
    split
    · rename_i empty
      have impossible := empty.symm.trans pending;cases impossible
    · rename_i h t same
      rcases List.cons.inj (pending.symm.trans same) with ⟨rfl,rfl⟩
      split
      · rename_i absent
        rw [registered] at absent;cases absent
      · rename_i found present
        cases Option.some.inj (registered.symm.trans present)
        split
        · rename_i paid
          rw [refused] at paid;cases paid
        · rfl
  | comparisonRefused head tail pending fee registered constructionPaid refused =>
    unfold run
    split
    · rename_i empty
      have impossible := empty.symm.trans pending;cases impossible
    · rename_i h t same
      rcases List.cons.inj (pending.symm.trans same) with ⟨rfl,rfl⟩
      split
      · rename_i absent
        rw [registered] at absent;cases absent
      · rename_i found present
        cases Option.some.inj (registered.symm.trans present)
        rw [dif_pos constructionPaid]
        dsimp only
        split
        · rename_i paid
          rw [refused] at paid;cases paid
        · rfl
  | searched head tail pending fee registered constructionPaid comparisonPaid =>
    unfold run
    split
    · rename_i empty
      have impossible := empty.symm.trans pending;cases impossible
    · rename_i h t same
      rcases List.cons.inj (pending.symm.trans same) with ⟨rfl,rfl⟩
      split
      · rename_i absent
        rw [registered] at absent;cases absent
      · rename_i found present
        cases Option.some.inj (registered.symm.trans present)
        rw [dif_pos constructionPaid,dif_pos comparisonPaid]

end Result

/-- The generated endpoint is cached with the result: recursive progress testing and
root readback do not rerun the paid quality fold. -/
private theorem cached_succeeded (cursor : Recovery.Cursor old oldDepth word) (fee : Action old) (units : Nat)
    (cache : Mandate.Replay.Materialized old.base old.scope cursor.before (invoice fee units)) :
    cache.succeeded = (attempt cursor fee units).succeeded := by
  rw [cache.succeeded_exact,cache.path_exact]

private theorem cached_charged (cursor : Recovery.Cursor old oldDepth word) (fee : Action old) (units : Nat)
    (cache : Mandate.Replay.Materialized old.base old.scope cursor.before (invoice fee units)) :
    Cursor.append cursor cache.output = charged cursor fee units := by
  unfold charged
  rw [cache.output_exact,cache.path_exact]

def SearchEvidence {cursor : Recovery.Cursor old oldDepth word} {position : Nat}
    (result : Result cursor position) (endpoint : Recovery.Cursor old oldDepth word) : Type :=
  match result with
  | .searched .. => {archive : SearchPaid.Archive old oldDepth word // archive.endpoint = endpoint}
  | _ => PUnit

def CatalogueEvidence {cursor : Recovery.Cursor old oldDepth word} {position : Nat}
    (result : Result cursor position) (endpoint : Recovery.Cursor old oldDepth word)
    (search : SearchEvidence result endpoint) : Type :=
  match result,search with
  | .comparisonRefused head _ _ fee _ _ _,_ =>
      {archive : CatalogueSource.Archive old oldDepth word //
        archive.stage = charged cursor fee 1 ∧ archive.actor = head.signer ∧ archive.original = cursor.residual}
  | .searched head _ _ fee _ _ _,searched =>
      {archive : CatalogueSource.Archive old oldDepth word //
        archive.stage = charged cursor fee 1 ∧ archive.actor = head.signer ∧ archive.original = cursor.residual ∧
        archive.execution.rows = searched.val.catalogue}
  | _,_ => PUnit

structure StageValue (cursor : Recovery.Cursor old oldDepth word) (position : Nat) where
  private mk ::
  result : Result cursor position
  generated : result = run cursor position
  endpoint : Recovery.Cursor old oldDepth word
  exact : endpoint = result.finish
  search : SearchEvidence result endpoint
  catalogue : CatalogueEvidence result endpoint search

def stageProgram (cursor : Recovery.Cursor old oldDepth word) (position : Nat) :
    StageProgram.Code (old := old) (oldDepth := oldDepth) (word := word) (StageValue cursor position) := by
  cases pending : cursor.residual with
  | nil => exact .done (.finished ⟨.finished pending,Result.canonical _,cursor,rfl,⟨⟩,⟨⟩⟩)
  | cons head tail =>
    cases registered : quote cursor head.signer position with
    | none => exact .done (.finished ⟨.unpriced head tail pending registered,Result.canonical _,cursor,rfl,⟨⟩,⟨⟩⟩)
    | some fee =>
      exact .replay cursor.before (invoice fee 1) fun first => by
        let built := Cursor.append cursor first.output
        have built_eq : built = charged cursor fee 1 := cached_charged cursor fee 1 first
        by_cases firstPaid : first.succeeded = true
        · have paid : (attempt cursor fee 1).succeeded = true :=
            (cached_succeeded cursor fee 1 first).symm.trans firstPaid
          exact .catalogue (CatalogueSource.source built head.signer cursor.residual) fun generatedCatalogue => by
            let catalogue := generatedCatalogue.rows
            let units := generatedCatalogue.units
            have catalogue_eq : catalogue = Search.repairs built.model built.before head.signer cursor.residual :=
              CatalogueSource.source_rows built head.signer cursor.residual generatedCatalogue
            have units_eq : units = comparisonUnits cursor.residual catalogue :=
              CatalogueSource.source_units built head.signer cursor.residual generatedCatalogue
            exact .replay built.before (invoice fee units) fun second => by
              let staged := Cursor.append built second.output
              have staged_eq : staged = charged built fee units := cached_charged built fee units second
              have canonical : (attempt (charged cursor fee 1) fee
                  (comparisonUnits cursor.residual (Search.repairs (charged cursor fee 1).model
                    (charged cursor fee 1).before head.signer cursor.residual))).succeeded = second.succeeded := by
                rw [←built_eq,←catalogue_eq,←units_eq]
                exact (cached_succeeded built fee units second).symm
              by_cases secondPaid : second.succeeded = true
              · have compared := canonical.trans secondPaid
                exact .done (.search ⟨staged,catalogue,fun searched => ⟨.searched head tail pending fee registered paid compared,
                  Result.canonical _,
                  searched.endpoint,by
                    rw [searched.endpoint_exact]
                    dsimp only [Result.finish]
                    rw [←built_eq,←catalogue_eq,←units_eq]
                    exact congrArg (fun point : Recovery.Cursor old oldDepth word => restored point catalogue) staged_eq,
                  ⟨⟨staged,catalogue,searched⟩,rfl⟩,
                  ⟨⟨built,head.signer,cursor.residual,generatedCatalogue⟩,built_eq,rfl,rfl,rfl⟩⟩⟩)
              · have refused := canonical.trans (Bool.eq_false_iff.mpr secondPaid)
                have unpaid : ¬ (attempt (charged cursor fee 1) fee
                    (comparisonUnits cursor.residual (Search.repairs (charged cursor fee 1).model
                      (charged cursor fee 1).before head.signer cursor.residual))).succeeded = true := by
                  rw [canonical];exact secondPaid
                exact .done (.finished ⟨.comparisonRefused head tail pending fee registered paid refused,
                  Result.canonical _,staged,by
                    dsimp only [Result.finish]
                    rw [←built_eq,←catalogue_eq,←units_eq]
                    exact staged_eq,⟨⟩,
                  ⟨⟨built,head.signer,cursor.residual,generatedCatalogue⟩,built_eq,rfl,rfl⟩⟩)
        · have refused := (cached_succeeded cursor fee 1 first).symm.trans (Bool.eq_false_iff.mpr firstPaid)
          have unpaid : ¬ (attempt cursor fee 1).succeeded = true := by
            rw [←cached_succeeded cursor fee 1 first];exact firstPaid
          exact .done (.finished ⟨.constructionRefused head tail pending fee registered refused,
            Result.canonical _,built,built_eq,⟨⟩,⟨⟩⟩)

structure Stage (cursor : Recovery.Cursor old oldDepth word) (position : Nat) where
  private mk ::
  execution : StageProgram.Execution (stageProgram cursor position)

def stage (cursor : Recovery.Cursor old oldDepth word) (position : Nat) : Stage cursor position :=
  ⟨StageProgram.execute (stageProgram cursor position)⟩

namespace Stage
variable {cursor : Recovery.Cursor old oldDepth word} {position : Nat} (made : Stage cursor position)
abbrev result := made.execution.value.result
abbrev generated := made.execution.value.generated
abbrev endpoint := made.execution.value.endpoint
abbrev exact := made.execution.value.exact
abbrev search := made.execution.value.search
abbrev catalogue := made.execution.value.catalogue

def fromExecution (execution : StageProgram.Execution (stageProgram cursor position)) : Stage cursor position :=
  ⟨execution⟩
theorem eq_default : made = stage cursor position := by
  rcases made with ⟨execution⟩
  change (⟨execution⟩ : Stage cursor position) = ⟨StageProgram.execute (stageProgram cursor position)⟩
  exact congrArg (fun actual => (⟨actual⟩ : Stage cursor position)) (execution.unique _)
end Stage

namespace Stage
variable {cursor : Recovery.Cursor old oldDepth word} {position : Nat} (made : Stage cursor position)
theorem preserves : Prefix cursor made.endpoint := by
  change Prefix cursor made.execution.value.endpoint
  rw [made.exact]
  exact made.result.preserves

theorem quiescent (stopped : ¬ made.endpoint.residual.length < cursor.residual.length) :
    made.result.Quiescent := by
  apply made.result.quiescent_of_no_progress
  rw [←made.exact]
  exact stopped

theorem released (progress : made.endpoint.residual.length < cursor.residual.length) :
    made.result.Released := by
  apply made.result.progress_requires_a_released_search
  rw [←made.exact]
  exact progress
end Stage
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering
