import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Enactment.Admitted.Ledger

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Enactment.Admitted

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (context : Context (input := input) (review := review) depth count prefixLimit renewalLimit sourceDepth sourceCount)
  (admission : InitialAdmissionAt context)

def occurrencePresentation : ConstructivePresentation
    ((sourceRoot context).toAuthoritativeRoot.toRoot.actual.OccurrenceAt context.visit.current)
    ((root context admission).toAuthoritativeRoot.toRoot.actual.OccurrenceAt (initial context)) where
  forward := fun _ => (root context admission).emitted (initial context)
  backward := fun _ => (sourceRoot context).emitted context.visit.current
  backward_forward := fun occurrence => (context.data.occurrence_eq_emitted context.visit.current occurrence).symm
  forward_backward := fun occurrence =>
    (Macro.Public.Source.occurrence_eq_emitted input depth count prefixLimit renewalLimit (oldPast context)
      (InitialAdmission.start admission) (family context) occurrence).symm

def targetAt (event : ExactTemporalCausalRootEventAt (sourceRoot context).toAuthoritativeRoot.toLedgerRoot context.visit) :
    SourceNativeSequentialActualActionTargetAt (sourceRoot context) context.visit event
      (sourceEntry context) (sourceAuthority context) := by
  rw [event.eq_generated]
  exact {
    TargetN := context.native.N
    translation := translation context
    TargetV := Macro.Public.Source.V input depth count prefixLimit renewalLimit (oldPast context) (InitialAdmission.start admission) (family context)
    targetRoot := root context admission
    targetTheory := TheoryState.rootSemantic context.native.N
    lawSurface_heq := HEq.rfl
    targetTheory_rootSemantic := ⟨id, fun _ => rfl⟩
    occurrencePresentation := occurrencePresentation context admission
    occurrence_commutes := rfl
    initialSupport_heq := heq_of_eq (initial_support_is_the_literal_original_current context admission)
    initialOpenLedger := initialLedger context admission
    initialOpenLedger_heq := initial_ledger_is_the_original_identity context admission
    initialLedger_responsibility_commutes := fun entry => (initial_ledger_preserves_every_original_row context admission entry).1.symm
    initialLedger_claim_commutes := fun entry => (initial_ledger_preserves_every_original_row context admission entry).2.1.symm
    initialLedger_budget_conservative := fun entry => (initial_ledger_preserves_every_original_row context admission entry).2.2.le
    initialLedgerNoFresh := fun entry => ⟨⟨(initialLedger context admission).backward entry,
      ⟨initial_ledger_has_no_fresh_row context admission entry⟩⟩⟩
    translatedSourceEntryRow := initialRow context admission (sourceEntry context)
    firstSuccessor := firstSuccessor context admission
    canonical_targetNextVisit_eq := Macro.Ingress.next_is_the_same_generated_successor (root context admission)
      (.finite (firstVisit context admission)) (firstSuccessor context admission)
    Answer := Macro.Raw.ResultAt context.native context.data context.reader context.germ
    answer := Macro.Raw.reportAt context.native context.data context.reader context.germ
    Receipt := fun answer => ULift.{3, 0} (PLift
      ((firstSuccessor context admission).targetCurrent = bodyNext context ∧
        (bodyNext context).account = context.native.account context.visit.current ∧
        answer = Macro.Raw.reportAt context.native context.data context.reader context.germ))
    receipt := ⟨⟨first_successor_is_the_actual_public_body context admission, rfl, rfl⟩⟩ }

def program : SourceNativeSequentialActualActionProgramAt (sourceRoot context) context.visit
    (sourceEntry context) (sourceAuthority context) where
  targetAt := targetAt context admission

def generated := (program context admission).generate
  ((sourceRoot context).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt context.visit)

#print axioms targetAt
#print axioms generated

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Enactment.Admitted
