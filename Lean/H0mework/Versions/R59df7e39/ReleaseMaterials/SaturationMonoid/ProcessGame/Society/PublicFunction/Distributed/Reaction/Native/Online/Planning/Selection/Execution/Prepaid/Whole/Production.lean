import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Reservation.Runtime
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Production
open Institutions.Capitalism.Universal.Source.Program
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {seed : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {driver : Feedback.Input seed.source.code} {cursor : Cursor seed driver}
  {pricing : Future.Recovery.Pricing (Future.Recovery.Action cursor.model)}
  {n : Nat} {reference : Term cursor} {actor : Party} {position : Nat}
  (scope : Scope cursor pricing n reference actor position)

structure Candidate where
  private mk ::
  own : Prefix.Own (paidPoint scope) actor
  before : own.before = scope.continuation.words

private theorem own_candidate_before
    (own : Prefix.Own (paidPoint scope) actor)
    (member : own ∈ Prefix.ownCandidates (paidPoint scope) actor scope.continuation.words) :
    own.before = scope.continuation.words := by
  obtain ⟨word,_,same⟩ := List.mem_map.mp member
  rw [←same]

def candidates : List (Candidate scope) :=
  (Prefix.ownCandidates (paidPoint scope) actor scope.continuation.words).attach.map fun own =>
    ⟨own.val,own_candidate_before scope own.val own.property⟩

/-- The received word is fixed before native replay; permission failure does not change that word. -/
def fromRequested (word : List (Future.Recovery.Action cursor.model)) :
    Option {candidate : Candidate scope // candidate.own.requested = word} :=
  (Prefix.issue (paidPoint scope) actor scope.continuation.words word).map fun issued =>
    ⟨⟨issued.val,issued.property.1⟩,issued.property.2⟩

theorem fromRequested_is_some_exactly_for_registered_personal_words
    (word : List (Future.Recovery.Action cursor.model)) :
    (fromRequested scope word).isSome = true ↔ word ∈ Prefix.ownWords (paidPoint scope) actor := by
  simpa only [fromRequested,Option.isSome_map] using
    Prefix.issue_is_some_exactly_for_registered_personal_words (paidPoint scope) actor scope.continuation.words word

theorem every_personal_registered_word_has_its_native_candidate
    (word : List (Future.Recovery.Action cursor.model))
    (bounded : word ∈ words cursor.source.val.code.actions cursor.source.val.code.actionLimit)
    (personal : Mandate.Replay.Personal actor word) :
    ∃ candidate ∈ candidates scope, candidate.own.requested = word := by
  obtain ⟨own,member,at_before,at_word⟩ :=
    Prefix.every_personal_registered_word_is_generated (paidPoint scope) actor scope.continuation.words word bounded personal
  refine ⟨⟨own,at_before⟩,?_,at_word⟩
  exact List.mem_map.mpr ⟨⟨own,member⟩,List.mem_attach _ _,rfl⟩

theorem the_empty_word_remains_generated :
    ∃ candidate ∈ candidates scope, candidate.own.requested = [] := by
  apply every_personal_registered_word_has_its_native_candidate scope []
  · exact (mem_words_iff _ _ _).mpr ⟨Nat.zero_le _,by simp⟩
  · intro request impossible
    cases impossible

namespace Candidate
variable {scope} (candidate : Candidate scope)
abbrev source := Whole.extendOwn scope candidate.own candidate.before

theorem action_is_the_exact_last_actual_source_event :
    ((comparisonPoint candidate.source).source.val.actualExecution (comparisonPoint scope).depth).submitted =
      candidate.own.execution.output := by
  have emitted := Prefix.at_word (paidPoint scope)
    (scope.continuation.words ++ [candidate.own.execution.output]) scope.continuation.words.length (by simp)
  have depth := Prefix.at_depth (paidPoint scope) scope.continuation.words
  have emittedWords : candidate.source.continuation.words = scope.continuation.words ++ [candidate.own.execution.output] :=
    scope.continuation.appendOwn_words candidate.own candidate.before
  change ((Prefix.pointFor (paidPoint scope) candidate.source.continuation.words).source.val.actualExecution
    (comparisonPoint scope).depth).submitted = _
  rw [emittedWords,depth]
  simpa only [List.getElem_append_right (Nat.le_refl _),Nat.sub_self,List.getElem_cons_zero] using emitted

theorem action_preserves_the_original_requests_and_exact_residual :
    candidate.own.execution.consumed ++ candidate.own.execution.residual = candidate.own.requested :=
  candidate.own.original_requests_are_exactly_consumed_or_residual

theorem every_emitted_action_remains_personally_controlled :
    Mandate.Replay.Personal actor candidate.own.execution.output := candidate.own.output_is_personal

variable (span : Nat)
def run : Reservation.Protocol cursor pricing n reference actor position span :=
  Reservation.resume cursor pricing n reference actor position span candidate.source

def read := Reservation.Runtime.read (candidate.run span)

theorem the_original_root_retains_the_generated_action_source_and_whole_window :
    (candidate.read span).execution.origin = some candidate.source ∧
    (candidate.read span).learning = (candidate.run span).endpoint ∧
    (candidate.read span).whole = Window.evaluate (candidate.run span).endpoint.model cursor.depth
      ((candidate.run span).endpoint.depth-cursor.depth) := by
  exact ⟨rfl,rfl,rfl⟩

theorem the_same_original_root_consumes_the_action_reservation_and_own_next :
    let record := candidate.run span
    let active := Reservation.Runtime.activated record
    (candidate.read span).execution.origin = some candidate.source ∧
    (candidate.read span).outstanding = record.result.obligations ∧
    HEq ((Reservation.Runtime.facade record).readoutAt active .computation)
      (active.tick.generated.projectionOutcome (.component ())) ∧
    HEq active.tick.generated.wholeLedgerWriteBack
      (active.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt active.current.visit.current) ∧
    active.tick.nextCurrent = (Reservation.Runtime.process record).stateAt
      ((Reservation.Runtime.process record).successor active.state) := by
  have whole := Reservation.Runtime.the_original_root_consumes_the_reserved_comparison_actual_prefix_full_obligations_and_own_next
    (candidate.run span)
  exact ⟨rfl,whole.2.1,whole.2.2.2.2.2.1,whole.2.2.2.2.2.2.1,whole.2.2.2.2.2.2.2⟩
end Candidate

variable (cursor pricing n reference actor position)
def prepare : Prepaid.Protocol cursor pricing n reference actor position ⊕
    (Σ scope : Scope cursor pricing n reference actor position,List (Candidate scope)) :=
  match Whole.prepare cursor pricing n reference actor position with
  | .inl header => .inl header
  | .inr scope => .inr ⟨scope,candidates scope⟩

/-- One full pool is reserved and compared before an own-action alternative is committed. -/
def selectFamily (span : Nat) : Reservation.Protocol cursor pricing n reference actor position span :=
  match Whole.prepare cursor pricing n reference actor position with
  | .inl _ => Reservation.invoke cursor pricing n reference actor position span
  | .inr scope => Reservation.resume cursor pricing n reference actor position span (withOwnFamily scope)

theorem the_joint_family_uses_the_original_root_whole_ledger_and_own_next (span : Nat) :
    let record := selectFamily cursor pricing n reference actor position span
    let active := Reservation.Runtime.activated record
    (Reservation.Runtime.read record).outstanding = record.result.obligations ∧
    HEq ((Reservation.Runtime.facade record).readoutAt active .computation)
      (active.tick.generated.projectionOutcome (.component ())) ∧
    HEq active.tick.generated.wholeLedgerWriteBack
      (active.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt active.current.visit.current) ∧
    active.tick.nextCurrent = (Reservation.Runtime.process record).stateAt
      ((Reservation.Runtime.process record).successor active.state) := by
  have whole := Reservation.Runtime.the_original_root_consumes_the_reserved_comparison_actual_prefix_full_obligations_and_own_next
    (selectFamily cursor pricing n reference actor position span)
  exact ⟨whole.2.1,whole.2.2.2.2.2.1,whole.2.2.2.2.2.2.1,whole.2.2.2.2.2.2.2⟩

/-- Quote every native own source without running or retaining a local selection winner. -/
def invoiceQuotations (scope : Scope cursor pricing n reference actor position) (span : Nat) :
    List (List (Future.Recovery.Action cursor.model) × Nat) :=
  (candidates scope).map fun candidate =>
    (candidate.own.requested, match Reservation.propose candidate.source span with
      | none => Work.workBudget candidate.source span
      | some ticket => ticket.bill.units)

/-- The common comparison payment and each selected branch's own invoice remain distinct events. -/
def selectInvoicedFamily (span : Nat) : Reservation.Protocol cursor pricing n reference actor position span :=
  match Whole.prepare cursor pricing n reference actor position with
  | .inl _ => Reservation.invoke cursor pricing n reference actor position span
  | .inr scope => Reservation.resume cursor pricing n reference actor position span
      (withOwnInvoices scope (invoiceQuotations cursor pricing n reference actor position scope span))

theorem the_invoiced_joint_family_uses_the_original_root_whole_ledger_and_own_next (span : Nat) :
    let record := selectInvoicedFamily cursor pricing n reference actor position span
    let active := Reservation.Runtime.activated record
    (Reservation.Runtime.read record).outstanding = record.result.obligations ∧
    HEq ((Reservation.Runtime.facade record).readoutAt active .computation)
      (active.tick.generated.projectionOutcome (.component ())) ∧
    HEq active.tick.generated.wholeLedgerWriteBack
      (active.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt active.current.visit.current) ∧
    active.tick.nextCurrent = (Reservation.Runtime.process record).stateAt
      ((Reservation.Runtime.process record).successor active.state) := by
  have whole := Reservation.Runtime.the_original_root_consumes_the_reserved_comparison_actual_prefix_full_obligations_and_own_next
    (selectInvoicedFamily cursor pricing n reference actor position span)
  exact ⟨whole.2.1,whole.2.2.2.2.2.1,whole.2.2.2.2.2.2.1,whole.2.2.2.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Production
