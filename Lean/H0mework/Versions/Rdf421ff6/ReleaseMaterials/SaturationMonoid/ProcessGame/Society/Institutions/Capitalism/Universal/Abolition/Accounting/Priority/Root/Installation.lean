import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Root.Renewal
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Policy.Execution
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Selection.ResidualSource

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Root.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim mechanism past nature response)
  (frame : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim)
  (proposal : RawEvent Party Good Port Technology Instrument)

local notation "native" => Renewal.native claim frame proposal
local notation "executed" => Gate.executableWord claim frame proposal
local notation "action" => Abolition.Accounting.Root.Reentry.generated claim native executed

def program : SourceNativeInquiryCompilationProgramAt (native).root frame.visit
    frame.basis.U7 frame.basis.calculus (native).root.toAuthoritativeRoot.source.lawSurface
    PUnit.unit (ULift.up.{1,0} ((native).root.emitted frame.visit.current))
    frame.row (native).authority where
  compile := fun _ => .actualAction action

def state : RootInquiryStateAt
    (DebtActivationWorld.ExtendedNetwork oldN (Responsibility.Family.activationLaw claim)) frame.V where
  root := (native).root
  visit := frame.visit
  U7 := frame.basis.U7
  calculus := frame.basis.calculus
  Query := PUnit
  entryAt := fun _ => frame.row
  authorityAt := fun _ => (native).authority
  compilationProgramAt := fun query => by cases query; exact program claim frame proposal
  compilationFaceAt := fun query => by
    cases query
    exact { projection := .inherited (.component Gate.Projection.compilation)
            active := PUnit.unit
            classifier_eq := rfl
            project_heq := HEq.rfl }
  u7RootDisposition_commutes := by intro query obstruction audit impossible; cases query; cases impossible

def presentation : RootInquiryStatePresentation :=
  ⟨_,_,RootInquiryEngineStateAt.create (state claim frame proposal)⟩

def successor : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim :=
  Abolition.Accounting.Root.Reentry.nextFrame claim native executed

theorem compiler_executes_only_the_source_gate_word :
    (state claim frame proposal).compileInquiry PUnit.unit = .actualAction action := rfl

theorem source_support_is_literal :
    Abolition.Accounting.Root.Reentry.Frame.support claim native =
      Abolition.Accounting.Root.Reentry.Frame.support claim frame := rfl

theorem successor_reads_the_actual_prefix_update :
    Abolition.Accounting.Root.Reentry.Frame.state claim (successor claim frame proposal) =
      Responsibility.Family.State.advance claim
        (Abolition.Accounting.Root.Reentry.Frame.state claim frame) frame.actualLaw executed := by
  exact Abolition.Accounting.Root.Reentry.next_frame_reads_the_actual_updated_state claim native executed

theorem successor_is_the_policy_update :
    Abolition.Accounting.Root.Reentry.Frame.state claim (successor claim frame proposal) =
      (Root.evaluation claim frame proposal).updated := by
  rw [successor_reads_the_actual_prefix_update]
  change Responsibility.Family.State.advance claim
    (Abolition.Accounting.Root.Reentry.Frame.state claim frame) frame.actualLaw
    (Root.evaluation claim frame proposal).executableWord = _
  unfold Policy.Evaluation.updated Root.evaluation
  rw [Input.old_state_is_literal,readLaw_eq]
  rfl

theorem every_executed_item_is_valid_in_the_original_physical_inventory :
    ∀ item ∈ frame.actualLaw.rawItems (Abolition.Accounting.Root.Reentry.Frame.state claim frame).raw executed,
      frame.actualLaw.Valid item.before item.request := by
  rw [Gate.executableWord_eq_original_evaluation]
  exact Policy.accepted_prefix_is_valid_in_the_original_inventory claim _ _ _
    (Policy.evaluate claim (Abolition.Accounting.Root.Reentry.Frame.state claim frame)
      frame.actualLaw frame.members proposal).accepted

theorem the_actual_accepted_word_is_the_original_executable_word :
    (Responsibility.Family.State.attempt claim (Abolition.Accounting.Root.Reentry.Frame.state claim frame)
      frame.actualLaw executed).actualWord = executed := by
  rw [Gate.executableWord_eq_original_evaluation]
  exact Policy.evaluation_actual_word_is_the_original_executable_word claim _ _ _
    (Policy.evaluate claim (Abolition.Accounting.Root.Reentry.Frame.state claim frame)
      frame.actualLaw frame.members proposal)

theorem actual_next_runs_the_original_physical_law_on_the_entire_accepted_prefix :
    (Abolition.Accounting.Root.Reentry.Frame.state claim (successor claim frame proposal)).raw =
      frame.actualLaw.next (Abolition.Accounting.Root.Reentry.Frame.state claim frame).raw executed := by
  rw [successor_reads_the_actual_prefix_update,Gate.executableWord_eq_original_evaluation]
  exact Policy.evaluation_updates_the_original_physical_cursor claim _ _ _
    (Policy.evaluate claim (Abolition.Accounting.Root.Reentry.Frame.state claim frame)
      frame.actualLaw frame.members proposal)

theorem the_generated_residual_is_positive_in_the_actual_next :
    match Root.renewalDecision claim frame proposal with
    | .residual issue _ => 0 < (Abolition.Accounting.Root.Reentry.Frame.state claim
        (successor claim frame proposal)).remaining issue.key
    | .admitted .. | .settled .. | .gate .. | .needs .. => True := by
  cases selected : Root.renewalDecision claim frame proposal with
  | residual issue noProgress =>
      rw [successor_is_the_policy_update]
      exact Selection.residual_exposes_a_positive_cell_in_the_actual_updated_row claim
        (Abolition.Accounting.Root.Reentry.Frame.state claim (Input.native claim frame proposal))
        (readLaw claim (Input.native claim frame proposal)) (readMembers claim (Input.native claim frame proposal))
        (Input.readProposal claim frame proposal) issue noProgress selected
  | admitted permit => trivial
  | settled paid needs declared noStop => trivial
  | gate issue => trivial
  | needs issue => trivial

theorem actual_process_resolution :
    type_of% (RootInquiryProcessNode.active_actualAction_resolution_eq
      (presentation claim frame proposal) PUnit.unit action rfl) :=
  RootInquiryProcessNode.active_actualAction_resolution_eq
    (presentation claim frame proposal) PUnit.unit action rfl

theorem actual_next_is_the_same_whole_ledger_successor :
    (RootInquiryProcessNode.answered (presentation claim frame proposal) PUnit.unit).erase =
      (⟨DebtActivationWorld.ExtendedNetwork oldN (Responsibility.Family.activationLaw claim),
        ⟨(successor claim frame proposal).V,(successor claim frame proposal).root.toAuthoritativeRoot,
          (successor claim frame proposal).visit⟩⟩ : AnyAuthoritativeRootCurrent) := by
  change (⟨DebtActivationWorld.ExtendedNetwork oldN (Responsibility.Family.activationLaw claim),
    (action).target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) = _
  exact congrArg (fun current =>
    (⟨DebtActivationWorld.ExtendedNetwork oldN (Responsibility.Family.activationLaw claim),current⟩ :
      AnyAuthoritativeRootCurrent)) (action).target.targetAnswerAndNext_next_eq

/-- The next root retains the decision made on its exact source input,
including the rejected tail and every original residual witness. -/
def successorGateFace : SourceNativeRootSemanticFaceAt
    (successor claim frame proposal).root (successor claim frame proposal).visit where
  projection := Abolition.Accounting.Root.Reentry.inquiryOldProjection claim native executed
    (.inherited (Gate.evaluationFace claim frame proposal).projection)
  active := (Gate.evaluationFace claim frame proposal).active
  classifier_eq := (Gate.evaluationFace claim frame proposal).classifier_eq

theorem successor_gate_is_the_literal_source_decision :
    HEq (successorGateFace claim frame proposal).rootRead (Root.evaluation claim frame proposal) := HEq.rfl

def successorRenewalFace : SourceNativeRootSemanticFaceAt
    (successor claim frame proposal).root (successor claim frame proposal).visit where
  projection := Abolition.Accounting.Root.Reentry.inquiryOldProjection claim native executed
    (Gate.renewalFace claim frame proposal).projection
  active := (Gate.renewalFace claim frame proposal).active
  classifier_eq := (Gate.renewalFace claim frame proposal).classifier_eq

theorem successor_renewal_is_the_literal_source_verdict :
    HEq (successorRenewalFace claim frame proposal).rootRead (Root.renewalDecision claim frame proposal) := HEq.rfl

theorem all_original_ledger_keys_are_preserved :
    type_of% (Abolition.Accounting.Root.Reentry.actual_keeps_every_original_responsibility_key
      claim native executed) :=
  Abolition.Accounting.Root.Reentry.actual_keeps_every_original_responsibility_key claim native executed

theorem the_old_network_support_is_retained :
    (Abolition.Accounting.Root.Reentry.Frame.support claim (successor claim frame proposal)).1 =
      (Abolition.Accounting.Root.Reentry.Frame.support claim frame).1 := by
  change (Abolition.Accounting.Root.Reentry.support claim native executed
    (Abolition.Accounting.Root.Compiler.successor
      (Abolition.Accounting.Root.Reentry.flow claim native executed) false).targetCurrent).1 = _
  exact congrArg (fun phase : Bool => (Abolition.Accounting.Root.Reentry.support claim native executed phase).1)
    (Abolition.Accounting.Root.Compiler.successor_current
      (Abolition.Accounting.Root.Reentry.flow claim native executed) false)

theorem the_native_liability_keeps_its_original_key :
    (successor claim frame proposal).row.1 = .inr (Responsibility.Family.activationLaw claim).debtId :=
  (successor claim frame proposal).rowKey

theorem no_original_financial_claim_is_erased :
    (Abolition.Accounting.Root.Reentry.Frame.state claim (successor claim frame proposal)).raw.claims =
      (Abolition.Accounting.Root.Reentry.Frame.state claim frame).raw.claims := by
  rw [successor_reads_the_actual_prefix_update]
  exact Responsibility.Family.State.actual_advance_retains_every_original_financial_claim _ _ _ _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Root.Installation
