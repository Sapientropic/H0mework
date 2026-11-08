import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceCapabilityAdmission
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageBudget

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageSourceAdmission
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (start : Cursor code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

-- The initial cursor owns the reference inventory; later installed rules are checked against it.
def check (stages : List (EventHistory.Stage (code := code))) (scope : Scope) : Bool :=
  (StageTrace.records start stages).all fun row => SourceCapabilityAdmission.check start.source vocabulary row.protocol scope

abbrev budget (scope : Scope) := SourceCapabilityAdmission.budget start.source vocabulary scope

theorem each_actual_issued_ballot_has_the_initial_source_capability
    (stages : List (EventHistory.Stage (code := code))) (scope : Scope)
    (checked : check start vocabulary stages scope = true) (body : StageBudget.Ballot (code := code))
    (inside : body ∈ StageBudget.ledger vocabulary start stages) (sameScope : body.scope = scope) :
    body.choice ∈ SourceCapabilityAdmission.choices start.source vocabulary scope body.key := by
  obtain ⟨row,member,position,made⟩ := StageBudget.ledger_origin vocabulary start stages body inside
  have labelled := (StageBudget.issued_is_in_the_actual_installed_local_word vocabulary start stages row member position body made).2.2
  have admitted := (List.all_eq_true.mp checked) row member
  have sameLabel : DeviationBudget.labelFor row.cursor.source vocabulary body.key =
      DeviationBudget.labelFor start.source vocabulary body.key := by
    funext request
    rfl
  rw [StageBudget.labels,sameLabel] at labelled
  have inTable := (ProtocolCapabilityBudget.mem_choices_iff start.source row.protocol.work.val vocabulary scope body.key body.choice).mpr
    ⟨row.before.frame.inbox body.key,by
      simpa only [sameScope,ProtocolCapabilityBudget.labels] using labelled⟩
  exact SourceCapabilityAdmission.an_admitted_choice_is_in_the_original_source start.source vocabulary row.protocol scope admitted body.key body.choice inTable

theorem conflicting_actual_ballots_from_admitted_stage_histories_expose_initial_capacity
    (left right : List (EventHistory.Stage (code := code))) (scope : Scope)
    (leftChecked : check start vocabulary left scope = true) (rightChecked : check start vocabulary right scope = true)
    (one two : StageBudget.Ballot (code := code))
    (first : one ∈ StageBudget.ledger vocabulary start left) (second : two ∈ StageBudget.ledger vocabulary start right)
    (sameKey : one.key = two.key) (scopeOne : one.scope = scope) (scopeTwo : two.scope = scope) (different : one.choice ≠ two.choice) :
    one.key ∈ SourceCapabilityAdmission.affected start.source vocabulary scope := by
  have a := each_actual_issued_ballot_has_the_initial_source_capability start vocabulary left scope leftChecked one first scopeOne
  have b := each_actual_issued_ballot_has_the_initial_source_capability start vocabulary right scope rightChecked two second scopeTwo
  rw [← sameKey] at b
  apply (ProtocolCapabilityBudget.mem_affected_iff start.source start.source.reference vocabulary scope one.key).mpr
  cases firstChoice : one.choice <;> cases secondChoice : two.choice <;> simp_all

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageSourceAdmission
