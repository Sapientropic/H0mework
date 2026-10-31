import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation.Source
import H0mework.Versions.R2.Foundation.Source.SequentialAction

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation Quantifiers.Joint

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))
  (visit : SourceNativeTemporalVisitAt (Runtime.Inquiry.root seed claim).toAuthoritativeRoot.toLedgerRoot)

local notation "oldRoot" => Origin.root seed claim visit
local notation "newRoot" => root seed claim visit
local notation "firstVisit" => Abolition.Accounting.Root.Compiler.initialVisit (flow seed claim visit)
local notation "first" => Abolition.Accounting.Root.Compiler.successor (flow seed claim visit) ()

def occurrencePresentation : ConstructivePresentation
    ((oldRoot).toAuthoritativeRoot.toRoot.actual.OccurrenceAt visit.current)
    ((newRoot).toAuthoritativeRoot.toRoot.actual.OccurrenceAt ()) where
  forward := fun _ => (newRoot).emitted ()
  backward := fun _ => (oldRoot).emitted visit.current
  backward_forward := fun occurrence => (Abolition.Accounting.Root.Compiler.occurrence_eq_emitted
    (Runtime.flow seed claim) occurrence).symm
  forward_backward := fun occurrence => (Abolition.Accounting.Root.Compiler.occurrence_eq_emitted
    (flow seed claim visit) occurrence).symm

variable (sourceAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt (Runtime.Inquiry.root seed claim)
  visit (Origin.row seed claim visit))

def targetAt (event : ExactTemporalCausalRootEventAt (oldRoot).toAuthoritativeRoot.toLedgerRoot visit) :
    SourceNativeSequentialActualActionTargetAt oldRoot visit event (Origin.row seed claim visit)
      (Origin.authority seed claim visit sourceAuthority) := by
  rw [event.eq_generated]
  exact {
    TargetN := NewN seed claim
    translation := translation seed claim
    TargetV := V seed claim visit
    targetRoot := newRoot
    targetTheory := TheoryState.rootSemantic (NewN seed claim)
    lawSurface_heq := HEq.rfl
    targetTheory_rootSemantic := ⟨id,fun _ => rfl⟩
    occurrencePresentation := occurrencePresentation seed claim visit
    occurrence_commutes := rfl
    initialSupport_heq := HEq.rfl
    initialOpenLedger := rows seed claim (sourceSupport seed claim visit)
    initialOpenLedger_heq := HEq.rfl
    initialLedger_responsibility_commutes := fun row =>
      (every_original_row_keeps_its_exact_relabelled_key seed claim (sourceSupport seed claim visit) row).symm
    initialLedger_claim_commutes := (translation seed claim).oldOpenClaim_commutes (sourceSupport seed claim visit)
    initialLedger_budget_conservative := fun row =>
      ((translation seed claim).oldOpenProgressBudget_commutes (sourceSupport seed claim visit) row).le
    initialLedgerNoFresh := fun row => ⟨⟨(rows seed claim (sourceSupport seed claim visit)).backward row,
      ⟨every_new_row_is_the_same_original_row seed claim (sourceSupport seed claim visit) row⟩⟩⟩
    translatedSourceEntryRow := Abolition.Accounting.Root.Compiler.generatedRow (flow seed claim visit) firstVisit
      ((rows seed claim (sourceSupport seed claim visit)).forward (Origin.row seed claim visit))
    firstSuccessor := first
    canonical_targetNextVisit_eq := Abolition.Root.Registered.Macro.Ingress.next_is_the_same_generated_successor
      (newRoot) firstVisit first
    Answer := Responsibility.Family.State seed.claim
    answer := familyState seed claim (Runtime.sharedAt seed claim visit.current)
    Receipt := fun answer => ULift.{3,0} (PLift
      (answer.raw = (Runtime.sharedAt seed claim visit.current).raw ∧
        answer.remaining = (Runtime.sharedAt seed claim visit.current).productive ∧
        answer.declared = (Runtime.sharedAt seed claim visit.current).productiveDeclared))
    receipt := ⟨⟨rfl,rfl,rfl⟩⟩ }

def program : SourceNativeSequentialActualActionProgramAt oldRoot visit (Origin.row seed claim visit)
    (Origin.authority seed claim visit sourceAuthority) where
  targetAt := targetAt seed claim visit sourceAuthority

def generated := (program seed claim visit sourceAuthority).generate
  ((oldRoot).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt visit)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation
