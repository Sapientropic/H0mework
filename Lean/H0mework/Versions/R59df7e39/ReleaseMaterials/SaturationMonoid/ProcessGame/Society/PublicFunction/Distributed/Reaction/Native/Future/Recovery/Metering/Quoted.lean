import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Replay.Program.Session
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.Quoted
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

structure Fees (Request : Type) where
  construction : List Request
  selection : List Request
  deriving DecidableEq

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {old : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {oldDepth : Nat} {word : List (Action old)}

def Supported (cursor : Recovery.Cursor old oldDepth word) (actor : Party) (fees : Fees (Action old)) : Prop :=
  fees.construction ∈ words cursor.source.val.code.actions cursor.source.val.code.actionLimit ∧
  fees.selection ∈ words cursor.source.val.code.actions cursor.source.val.code.actionLimit ∧
  ∀ request ∈ fees.construction ++ fees.selection, IsFee cursor actor request

instance (cursor : Recovery.Cursor old oldDepth word) (actor : Party) (fees : Fees (Action old)) :
    Decidable (Supported cursor actor fees) := by unfold Supported;infer_instance

def quote (cursor : Recovery.Cursor old oldDepth word) (actor : Party) (fees : Fees (Action old)) :
    Option (Fees (Action old)) := if Supported cursor actor fees then some fees else none

theorem quote_is_the_original_two_registered_personal_words
    (cursor : Recovery.Cursor old oldDepth word) (actor : Party) (fees found : Fees (Action old))
    (registered : quote cursor actor fees = some found) : found = fees ∧ Supported cursor actor fees := by
  unfold quote at registered
  split at registered
  next supported => exact ⟨(Option.some.inj registered).symm,supported⟩
  next => cases registered

abbrev invoice (fee : List (Action old)) (units : Nat) := (List.replicate units fee).flatten
abbrev attempt (cursor : Recovery.Cursor old oldDepth word) (fee : List (Action old)) (units : Nat) :=
  Mandate.Replay.compile old.base old.scope cursor.before (invoice fee units)
abbrev charged (cursor : Recovery.Cursor old oldDepth word) (fee : List (Action old)) (units : Nat) :=
  Metering.Cursor.append cursor (attempt cursor fee units).output

theorem a_refused_word_invoice_is_its_exact_actual_raw_obstruction
    (cursor : Recovery.Cursor old oldDepth word) (fee : List (Action old)) (units : Nat)
    (refused : (attempt cursor fee units).succeeded = false) :
    ∃ item ∈ (charged cursor fee units).source.val.code.law.rawItems
        ((charged cursor fee units).source.val.actualExecution cursor.depth).before
        ((charged cursor fee units).source.val.actualExecution cursor.depth).submitted,
      item.index = (attempt cursor fee units).consumed.length ∧
        ¬ (charged cursor fee units).source.val.code.law.Valid item.before item.request := by
  rw [Metering.Cursor.submitted,Metering.Cursor.before]
  change ∃ item ∈ cursor.source.val.code.law.rawItems cursor.before (attempt cursor fee units).output,
    item.index = _ ∧ ¬ cursor.source.val.code.law.Valid item.before item.request
  rw [cursor.source.property.1]
  exact (attempt cursor fee units).failure_is_an_actual_raw_item refused

inductive Result (cursor : Recovery.Cursor old oldDepth word) (tariffPosition : Fees (Action old)) where
  | finished (empty : cursor.residual = [])
  | unpriced (head : Action old) (tail : List (Action old)) (pending : cursor.residual = head::tail)
      (absent : quote cursor head.signer tariffPosition = none)
  | constructionRefused (head : Action old) (tail : List (Action old)) (pending : cursor.residual = head::tail)
      (fee : Fees (Action old)) (registered : quote cursor head.signer tariffPosition = some fee)
      (refused : (attempt cursor fee.construction 1).succeeded = false)
  | comparisonRefused (head : Action old) (tail : List (Action old)) (pending : cursor.residual = head::tail)
      (fee : Fees (Action old)) (registered : quote cursor head.signer tariffPosition = some fee)
      (constructionPaid : (attempt cursor fee.construction 1).succeeded = true)
      (refused : (attempt (charged cursor fee.construction 1) fee.selection
        (comparisonUnits cursor.residual (Search.repairs (charged cursor fee.construction 1).model
          (charged cursor fee.construction 1).before head.signer cursor.residual))).succeeded = false)
  | searched (head : Action old) (tail : List (Action old)) (pending : cursor.residual = head::tail)
      (fee : Fees (Action old)) (registered : quote cursor head.signer tariffPosition = some fee)
      (constructionPaid : (attempt cursor fee.construction 1).succeeded = true)
      (comparisonPaid : (attempt (charged cursor fee.construction 1) fee.selection
        (comparisonUnits cursor.residual (Search.repairs (charged cursor fee.construction 1).model
          (charged cursor fee.construction 1).before head.signer cursor.residual))).succeeded = true)

/-- The source checks both quoted words before any catalogue is released. -/
def run (cursor : Recovery.Cursor old oldDepth word) (tariffPosition : Fees (Action old)) : Result cursor tariffPosition :=
  match pending : cursor.residual with
  | [] => .finished pending
  | head::tail => match registered : quote cursor head.signer tariffPosition with
    | none => .unpriced head tail pending registered
    | some fee =>
      if paid : (attempt cursor fee.construction 1).succeeded = true then
        let built := charged cursor fee.construction 1
        let catalogue := Search.repairs built.model built.before head.signer cursor.residual
        if compared : (attempt built fee.selection (comparisonUnits cursor.residual catalogue)).succeeded = true then
          .searched head tail pending fee registered paid compared
        else .comparisonRefused head tail pending fee registered paid (Bool.eq_false_iff.mpr compared)
      else .constructionRefused head tail pending fee registered (Bool.eq_false_iff.mpr paid)

namespace Result
variable {cursor : Recovery.Cursor old oldDepth word} {tariffPosition : Fees (Action old)}

def finish : Result cursor tariffPosition → Recovery.Cursor old oldDepth word
  | .finished _ | .unpriced .. => cursor
  | .constructionRefused _ _ _ fee _ _ => charged cursor fee.construction 1
  | .comparisonRefused head _ _ fee _ _ _ =>
      let built := charged cursor fee.construction 1
      charged built fee.selection (comparisonUnits cursor.residual (Search.repairs built.model built.before head.signer cursor.residual))
  | .searched head _ _ fee _ _ _ =>
      let built := charged cursor fee.construction 1
      let catalogue := Search.repairs built.model built.before head.signer cursor.residual
      restored (charged built fee.selection (comparisonUnits cursor.residual catalogue)) catalogue

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
      (attempt cursor fee.construction 1).succeeded = true ∧
      (attempt (charged cursor fee.construction 1) fee.selection (comparisonUnits cursor.residual
        (Search.repairs (charged cursor fee.construction 1).model (charged cursor fee.construction 1).before head.signer cursor.residual))).succeeded = true := by
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
      let built := charged cursor fee.construction 1
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
  | .constructionRefused _ _ _ fee _ _ => (attempt cursor fee.construction 1).succeeded = false
  | .comparisonRefused head _ _ fee _ _ _ =>
      let built := charged cursor fee.construction 1
      (attempt built fee.selection (comparisonUnits cursor.residual
        (Search.repairs built.model built.before head.signer cursor.residual))).succeeded = false
  | .searched head _ _ fee _ _ _ =>
      let built := charged cursor fee.construction 1
      let catalogue := Search.repairs built.model built.before head.signer cursor.residual
      let staged := charged built fee.selection (comparisonUnits cursor.residual catalogue)
      ∀ preparation ∈ catalogue, (rank staged preparation).value = 0

theorem quiescent_of_no_progress (made : Result cursor tariffPosition)
    (stopped : ¬ made.finish.residual.length < cursor.residual.length) : made.Quiescent := by
  cases made with
  | finished empty => exact empty
  | unpriced _ _ _ absent => exact absent
  | constructionRefused _ _ _ _ _ refused => exact refused
  | comparisonRefused _ _ _ _ _ _ refused => exact refused
  | searched head tail pending fee registered constructionPaid comparisonPaid =>
      let built := charged cursor fee.construction 1
      let catalogue := Search.repairs built.model built.before head.signer cursor.residual
      let staged := charged built fee.selection (comparisonUnits cursor.residual catalogue)
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
private theorem cached_succeeded (cursor : Recovery.Cursor old oldDepth word) (fee : List (Action old)) (units : Nat)
    (cache : Mandate.Replay.Materialized old.base old.scope cursor.before (invoice fee units)) :
    cache.succeeded = (attempt cursor fee units).succeeded := by
  rw [cache.succeeded_exact,cache.path_exact]

private theorem cached_charged (cursor : Recovery.Cursor old oldDepth word) (fee : List (Action old)) (units : Nat)
    (cache : Mandate.Replay.Materialized old.base old.scope cursor.before (invoice fee units)) :
    Metering.Cursor.append cursor cache.output = charged cursor fee units := by
  unfold charged
  rw [cache.output_exact,cache.path_exact]

def SearchEvidence {cursor : Recovery.Cursor old oldDepth word} {position : Fees (Action old)}
    (result : Result cursor position) (endpoint : Recovery.Cursor old oldDepth word) : Type :=
  match result with
  | .searched .. => {archive : SearchPaid.Archive old oldDepth word // archive.endpoint = endpoint}
  | _ => PUnit

def CatalogueEvidence {cursor : Recovery.Cursor old oldDepth word} {position : Fees (Action old)}
    (result : Result cursor position) (endpoint : Recovery.Cursor old oldDepth word)
    (search : SearchEvidence result endpoint) : Type :=
  match result,search with
  | .comparisonRefused head _ _ fee _ _ _,_ =>
      {archive : CatalogueSource.Archive old oldDepth word //
        archive.stage = charged cursor fee.construction 1 ∧ archive.actor = head.signer ∧ archive.original = cursor.residual}
  | .searched head _ _ fee _ _ _,searched =>
      {archive : CatalogueSource.Archive old oldDepth word //
        archive.stage = charged cursor fee.construction 1 ∧ archive.actor = head.signer ∧ archive.original = cursor.residual ∧
        archive.execution.rows = searched.val.catalogue}
  | _,_ => PUnit

structure StageValue (cursor : Recovery.Cursor old oldDepth word) (position : Fees (Action old)) where
  private mk ::
  result : Result cursor position
  generated : result = run cursor position
  endpoint : Recovery.Cursor old oldDepth word
  exact : endpoint = result.finish
  search : SearchEvidence result endpoint
  catalogue : CatalogueEvidence result endpoint search

def stageProgram (cursor : Recovery.Cursor old oldDepth word) (position : Fees (Action old)) :
    StageProgram.Code (old := old) (oldDepth := oldDepth) (word := word) (StageValue cursor position) := by
  cases pending : cursor.residual with
  | nil => exact .done (.finished ⟨.finished pending,Result.canonical _,cursor,rfl,⟨⟩,⟨⟩⟩)
  | cons head tail =>
    cases registered : quote cursor head.signer position with
    | none => exact .done (.finished ⟨.unpriced head tail pending registered,Result.canonical _,cursor,rfl,⟨⟩,⟨⟩⟩)
    | some fee =>
      exact .replay cursor.before (invoice fee.construction 1) fun first => by
        let built := Metering.Cursor.append cursor first.output
        have built_eq : built = charged cursor fee.construction 1 := cached_charged cursor fee.construction 1 first
        by_cases firstPaid : first.succeeded = true
        · have paid : (attempt cursor fee.construction 1).succeeded = true :=
            (cached_succeeded cursor fee.construction 1 first).symm.trans firstPaid
          exact .catalogue (CatalogueSource.source built head.signer cursor.residual) fun generatedCatalogue => by
            let catalogue := generatedCatalogue.rows
            let units := generatedCatalogue.units
            have catalogue_eq : catalogue = Search.repairs built.model built.before head.signer cursor.residual :=
              CatalogueSource.source_rows built head.signer cursor.residual generatedCatalogue
            have units_eq : units = comparisonUnits cursor.residual catalogue :=
              CatalogueSource.source_units built head.signer cursor.residual generatedCatalogue
            exact .replay built.before (invoice fee.selection units) fun second => by
              let staged := Metering.Cursor.append built second.output
              have staged_eq : staged = charged built fee.selection units := cached_charged built fee.selection units second
              have canonical : (attempt (charged cursor fee.construction 1) fee.selection
                  (comparisonUnits cursor.residual (Search.repairs (charged cursor fee.construction 1).model
                    (charged cursor fee.construction 1).before head.signer cursor.residual))).succeeded = second.succeeded := by
                rw [←built_eq,←catalogue_eq,←units_eq]
                exact (cached_succeeded built fee.selection units second).symm
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
                have unpaid : ¬ (attempt (charged cursor fee.construction 1) fee.selection
                    (comparisonUnits cursor.residual (Search.repairs (charged cursor fee.construction 1).model
                      (charged cursor fee.construction 1).before head.signer cursor.residual))).succeeded = true := by
                  rw [canonical];exact secondPaid
                exact .done (.finished ⟨.comparisonRefused head tail pending fee registered paid refused,
                  Result.canonical _,staged,by
                    dsimp only [Result.finish]
                    rw [←built_eq,←catalogue_eq,←units_eq]
                    exact staged_eq,⟨⟩,
                  ⟨⟨built,head.signer,cursor.residual,generatedCatalogue⟩,built_eq,rfl,rfl⟩⟩)
        · have refused := (cached_succeeded cursor fee.construction 1 first).symm.trans (Bool.eq_false_iff.mpr firstPaid)
          have unpaid : ¬ (attempt cursor fee.construction 1).succeeded = true := by
            rw [←cached_succeeded cursor fee.construction 1 first];exact firstPaid
          exact .done (.finished ⟨.constructionRefused head tail pending fee registered refused,
            Result.canonical _,built,built_eq,⟨⟩,⟨⟩⟩)

structure Stage (cursor : Recovery.Cursor old oldDepth word) (position : Fees (Action old)) where
  private mk ::
  execution : StageProgram.Execution (stageProgram cursor position)

def stage (cursor : Recovery.Cursor old oldDepth word) (position : Fees (Action old)) : Stage cursor position :=
  ⟨StageProgram.execute (stageProgram cursor position)⟩

namespace Stage
variable {cursor : Recovery.Cursor old oldDepth word} {position : Fees (Action old)} (made : Stage cursor position)
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
variable {cursor : Recovery.Cursor old oldDepth word} {position : Fees (Action old)} (made : Stage cursor position)
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
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.Quoted
