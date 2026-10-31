import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Action.Runtime.Process
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Source.Actors

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Action.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion SourceNativeInquiryRuntime
open DebtActivationWorld DebtActivationLedger
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (frame : Financial.Installation.NativeFrame input)
  (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (claim : Responsibility.Family.Claim mechanism past nature response)
  (origin : Source.OriginAt input frame visit claim)
  (word : RawEvent Party Good Port Technology Instrument)
  (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt frame.root visit (Source.sourceEntry input frame visit))
  [Finite frame.root.toAuthoritativeRoot.source.projectionLaw.Projection]

local notation "installed" => Installation.native input frame visit claim word
local notation "admission" => Installation.generated input frame visit claim origin word authority
local notation "F" => Source.flow input installed visit claim word
local notation "newRoot" => Source.Inquiry.root input installed visit claim word
local notation "actualRuntime" => runtime input frame visit claim origin word authority

def needFace : SourceNativeRootSemanticFaceAt newRoot (Source.Inquiry.temporalAt input installed visit claim word 1) where
  projection := .component .needs
  active := PUnit.unit
  classifier_eq := rfl

def verdictFace : SourceNativeRootSemanticFaceAt newRoot (Source.Inquiry.temporalAt input installed visit claim word 1) where
  projection := .component .verdict
  active := PUnit.unit
  classifier_eq := rfl

/-- One exact source occurrence owns the financial classification, controller
lineage, complete liability birth, actual repair and independent needs read. -/
structure SameSourceAccountingAt : Prop where
  source_input : (Installation.inputFace input frame visit claim word).rootRead = word
  compiled_input : (Installation.state input frame visit claim origin word authority).compileInquiry PUnit.unit =
    .debtAdmission (Action.generated input installed visit claim
      (Installation.installedOrigin input frame visit claim origin word)
      (Installation.inputFace input frame visit claim word).rootRead
      (Installation.authority input frame visit claim word authority))
  consumed : DebtAdmissionActualActionResumptionAt admission actualRuntime 0
  inventory : (Control.responseExecution mechanism past nature response).items =
    input.law.rawItems (ProgrammeSource.rawCurrent input (Source.originalVisit input frame visit).current)
      (ProgrammeSource.rawEvent input (Source.originalVisit input frame visit).current)
  original_past : past = Source.originalPastWords input frame visit
  profit4 : ∀ before after person good, Source.OriginalFourComponents input frame visit before after person good
  controller_lineage : ∀ gate : Responsibility.GateOccurrence mechanism past nature response,
    (Source.ProgrammeFace.ActualBirth.lookup input (Source.originalVisit input frame visit)
      (gate.controller mechanism past nature response)).isSome = true
  whole_ledger : HEq (admission).target.firstSuccessor.ledgerEvolution.destination
    (jointStepLedgerEvolution (admission).target.sourceSuccessor.ledgerEvolution
      (Source.sourceEntry input installed visit) (admission).target.stepEvent.step).destination
  declaration_preserves_matrix : (Source.declared input installed visit claim).remaining =
    (Source.initialState input installed visit claim).remaining
  observed : HEq ((actualRuntime).tickAt 2).answer (Source.observed input frame visit claim word)
  active_next : ((actualRuntime).stateAt 2).engine.node = .active (target input frame visit claim word 1)
  visible_material : HEq (verdictFace input frame visit claim word).rootRead
    (Responsibility.Family.adjudicate claim (Source.declared input frame visit claim) (Source.actualLaw input) word)
  visible_needs : HEq (needFace input frame visit claim word).rootRead
    (Responsibility.Family.inspectActualNeeds claim (Source.declared input frame visit claim) (Source.actualLaw input) word
      (Financial.Installation.observe input (frame.cursor visit.current)).members)
  no_global_terminal : (Responsibility.Family.activationLaw claim).SupportTerminalAt
    (Source.observed input frame visit claim word) → False

theorem the_original_source_installs_and_consumes_its_complete_accounting :
    SameSourceAccountingAt input frame visit claim origin word authority where
  source_input := rfl
  compiled_input := rfl
  consumed := ⟨the_compulsory_admission_is_consumed_by_the_named_canonical_runtime
    input frame visit claim origin word authority⟩
  inventory := Source.the_assessed_inventory_is_the_literal_original_execution input frame visit claim origin
  original_past := origin.history
  profit4 := Source.the_same_original_profit_read_has_all_four_components input frame visit
  controller_lineage := fun gate => Source.ProgrammeFace.ActualBirth.current_participation_generates_birth _ _ _
    (Source.the_responsible_controller_is_present_on_its_original_occurrence input frame visit claim origin gate)
  whole_ledger := (admission).target.firstDestination_heq
  declaration_preserves_matrix := rfl
  observed := the_actual_observed_answer_is_the_same_physical_update input frame visit claim origin word authority
  active_next := the_actual_repair_then_keeps_its_residual_root_active input frame visit claim origin word authority
  visible_material := HEq.rfl
  visible_needs := HEq.rfl
  no_global_terminal := fun impossible => nomatch impossible

#print axioms the_original_source_installs_and_consumes_its_complete_accounting

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Action.Runtime
