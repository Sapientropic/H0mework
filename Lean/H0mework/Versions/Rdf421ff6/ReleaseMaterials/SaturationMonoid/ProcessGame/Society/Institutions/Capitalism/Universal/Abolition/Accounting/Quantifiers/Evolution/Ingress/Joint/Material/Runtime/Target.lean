import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Ingress

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation Quantifiers.Joint
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

local notation "oldRoot" => Origin.root seed claim
local notation "newRoot" => Inquiry.root seed claim
local notation "initialVisit" => Abolition.Accounting.Root.Compiler.initialVisit (flow seed claim)
local notation "first" => Abolition.Accounting.Root.Compiler.successor (flow seed claim) (initial seed)

def targetAt (event : ExactTemporalCausalRootEventAt (oldRoot).toAuthoritativeRoot.toLedgerRoot (Admission.nextVisit seed claim)) :
    SourceNativeSequentialActualActionTargetAt oldRoot (Admission.nextVisit seed claim) event
      (Admission.nextRow seed claim) (Origin.authority seed claim) := by
  rw [event.eq_generated]
  exact {
    TargetN := Admission.N seed claim
    translation := Financial.Installation.Ingress.identityTranslation (Admission.N seed claim)
    TargetV := V seed claim
    targetRoot := newRoot
    targetTheory := TheoryState.rootSemantic (Admission.N seed claim)
    lawSurface_heq := HEq.rfl
    targetTheory_rootSemantic := ⟨id,fun _ => rfl⟩
    occurrencePresentation := occurrencePresentation seed claim
    occurrence_commutes := rfl
    initialSupport_heq := heq_of_eq (Inquiry.the_initial_support_is_the_literal_original_declared_whole_account seed claim).symm
    initialOpenLedger := initialLedger seed claim
    initialOpenLedger_heq := initialLedger_heq seed claim
    initialLedger_responsibility_commutes := fun row => (initialLedger_key seed claim row).symm
    initialLedger_claim_commutes := fun row => (initialLedger_claim seed claim row).symm
    initialLedger_budget_conservative := fun row => (initialLedger_budget seed claim row).le
    initialLedgerNoFresh := fun row => ⟨⟨(initialLedger seed claim).backward row,⟨initialLedger_no_fresh seed claim row⟩⟩⟩
    translatedSourceEntryRow := Abolition.Accounting.Root.Compiler.generatedRow (flow seed claim) initialVisit
      ((initialLedger seed claim).forward (Admission.nextRow seed claim))
    firstSuccessor := first
    canonical_targetNextVisit_eq := Abolition.Root.Registered.Macro.Ingress.next_is_the_same_generated_successor
      (newRoot) initialVisit first
    Answer := FinancialCurrent seed
    answer := next seed claim (initial seed)
    Receipt := fun answer => ULift.{3,0} (PLift
      (answer.bodyPaid = true ∧ answer.account = Background.nativeAccount seed ∧
        (sharedAt seed claim answer).raw = (Execution.Selected.result seed claim).next.raw ∧
        (Planning.Enough seed claim (Material.shared seed claim) →
          Planning.ActualSuccess seed claim (Material.shared seed claim) (Material.word seed claim))))
    receipt := ⟨⟨(the_body_is_paid_once_before_any_native_item seed claim).1,
      (the_body_is_paid_once_before_any_native_item seed claim).2,
      (congrArg (fun current : Current seed claim => current.raw)
        (the_first_material_next_is_the_source_selected_actual_next seed claim)).trans
          (Execution.Selected.physical_and_financial_execution_have_the_same_material_next seed claim).symm,
      Planning.sufficient_source_resources_force_the_actual_shared_payment seed claim (Material.shared seed claim)⟩⟩ }

def program : SourceNativeSequentialActualActionProgramAt oldRoot (Admission.nextVisit seed claim)
    (Admission.nextRow seed claim) (Origin.authority seed claim) where
  targetAt := targetAt seed claim

def generated := (program seed claim).generate
  ((oldRoot).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt (Admission.nextVisit seed claim))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime
