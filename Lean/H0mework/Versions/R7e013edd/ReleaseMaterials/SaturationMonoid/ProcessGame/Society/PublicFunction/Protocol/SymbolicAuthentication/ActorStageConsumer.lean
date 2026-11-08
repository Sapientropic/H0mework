import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ActorStageQuorum

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ActorStageConsumer
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (start : Cursor code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

def conflict (one two : StageBudget.Ballot (code := code)) : Bool :=
  decide (one.actor = two.actor ∧ one.scope = two.scope ∧ one.choice ≠ two.choice)
def evidence (stages : List (EventHistory.Stage (code := code))) :=
  ((StageBudget.ledger vocabulary start stages).product (StageBudget.ledger vocabulary start stages)).filter
    fun pair => conflict pair.1 pair.2

theorem each_evidence_pair_retains_both_actual_paid_origins_and_one_affected_actor
    (stages : List (EventHistory.Stage (code := code))) (one two : StageBudget.Ballot (code := code))
    (member : (one,two) ∈ evidence start vocabulary stages) :
    (∃ row ∈ StageTrace.records start stages, ∃ position, StageBudget.issued vocabulary row position = some one) ∧
    (∃ row ∈ StageTrace.records start stages, ∃ position, StageBudget.issued vocabulary row position = some two) ∧
    one.actor = two.actor ∧ one.scope = two.scope ∧ one.choice ≠ two.choice ∧
    one.actor ∈ ActorStageEnvelope.affected start vocabulary stages one.scope := by
  obtain ⟨members,different⟩ := List.mem_filter.mp member
  obtain ⟨first,second⟩ := List.mem_product.mp members
  obtain ⟨actor,scope,choice⟩ := of_decide_eq_true different
  exact ⟨StageBudget.ledger_origin vocabulary start stages one first,
    StageBudget.ledger_origin vocabulary start stages two second,actor,scope,choice,
    ActorStageEnvelope.conflicting_actual_aliases_or_cuts_spend_one_affected_identity start vocabulary stages
      one.scope one two first second actor rfl scope.symm choice⟩

omit [DecidableEq Port] [DecidableEq Technology] in
theorem different_phases_do_not_create_actor_equivocation
    (one two : StageBudget.Ballot (code := code)) (different : one.scope.phase ≠ two.scope.phase) :
    conflict one two = false := by
  simp only [conflict,decide_eq_false_iff_not]
  rintro ⟨_,same,_⟩
  exact different (congrArg Scope.phase same)

abbrev final (stages : List (EventHistory.Stage (code := code))) := EventHistory.execute start stages
abbrev facade (stages : List (EventHistory.Stage (code := code))) :=
  Feedback.Runtime.facade (final start stages).source (final start stages).entry rfl rfl

theorem the_actual_source_keeps_all_financial_rows_whole_ledger_and_literal_next
    (stages : List (EventHistory.Stage (code := code))) :
    let runtime := (facade start stages).seed.advance (EventStep.boundary (final start stages))
    (∀ row ∈ StageTrace.records start stages,
      (Financial.inventoryAt (final start stages).source.input
        (ProgrammeHistory.visitAt (final start stages).source.input (EventStep.boundary row.cursor))).filterMap
        (Financial.InstructionOrigin.instruction? (final start stages).source.input) = StageTrace.items row) ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    runtime.tick.nextCurrent = (facade start stages).process.stateAt ((facade start stages).process.successor runtime.state) := by
  have rooted := (facade start stages).readoutAt_factorizes
    ((facade start stages).seed.advance (EventStep.boundary (final start stages))) .feedback
  exact ⟨fun row member => StageTrace.final_financial_inventory_is_the_original_record_items _ _ row member,
    rooted.2.2.1,rooted.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ActorStageConsumer
