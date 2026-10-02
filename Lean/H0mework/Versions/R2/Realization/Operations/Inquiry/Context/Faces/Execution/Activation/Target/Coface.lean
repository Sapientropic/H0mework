import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Programme

/-! Whole admission descriptors are transported along the source coface.
The initial rows and full first write are retained; canonical next is read
from the same generated first successor. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation
open RootInquiryCompletion SourceOperationEffects
section TargetTransport
private theorem target_generated_next {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}} (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
    (successor : SourceNativeLedgerGeneratedSuccessorAt (root.emitted visit.current)
      (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current)) :
    root.generatedNextCurrentAt visit =
      ⟨V, root.toAuthoritativeRoot, visit.next successor.next_eq⟩ := by
  generalize same : root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current = generated at successor ⊢
  cases generated with
  | nativeWrite write structural target evolution =>
      exact root.generatedNextCurrentAt_eq_nativeWriteBranch visit write structural target evolution same successor.next_eq
  | relationWrite write structural target evolution =>
      exact root.generatedNextCurrentAt_eq_relationWriteBranch visit write structural target evolution same successor.next_eq
  | continuedTransport write structural target evolution =>
      exact root.generatedNextCurrentAt_eq_continuedTransportBranch visit write structural target evolution same successor.next_eq
  | borromeanRedirect write structural target evolution =>
      exact root.generatedNextCurrentAt_eq_borromeanRedirectBranch visit write structural target evolution same successor.next_eq
  | faithfulTerminal terminal structural evolution => exact nomatch successor

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {sourceRoot : SourceNativeLivingRootClosure N V}
variable {sourceVisit : SourceNativeTemporalVisitAt sourceRoot.toAuthoritativeRoot.toLedgerRoot}
variable {sourceEvent : ExactTemporalCausalRootEventAt sourceRoot.toAuthoritativeRoot.toLedgerRoot sourceVisit}
variable {sourceEntry : OpenResponsibilityAt N
  (sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
    (sourceRoot.emitted sourceVisit.current))}
variable {sourceAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt sourceRoot sourceVisit sourceEntry}
variable (target : SourceNativeDebtAdmissionActualActionTargetAt sourceRoot sourceVisit sourceEvent sourceEntry sourceAuthority)
variable (component : SourceNativeProjectionLaw target.targetRoot.source.base.restructuringSource.toLedgerSource)
abbrev targetCoface : SourceNativeDebtAdmissionActualActionTargetAt sourceRoot sourceVisit sourceEvent sourceEntry sourceAuthority where
  law := target.law
  sourceState := target.sourceState
  stepEvent := target.stepEvent
  sourceSuccessor := target.sourceSuccessor
  TargetV := target.TargetV
  targetRoot := target.targetRoot.withProjectionCoface component
  initialSupport_eq := target.initialSupport_eq
  initialOldRow := target.initialOldRow
  initialBornRow := target.initialBornRow
  firstSuccessor := target.firstSuccessor
  firstSupport_eq := target.firstSupport_eq
  firstDestination_heq := target.firstDestination_heq
  oldProjection := fun projection => SourceNativeProjectionCoface.inherited (target.oldProjection projection)
  oldProjection_injective := by
    intro first second same
    exact target.oldProjection_injective (SourceNativeProjectionCoface.inherited.inj same)
  oldOutcome_heq := fun projection =>
    ((SourceNativeProjectionLaw.InstallationAt.inheritedCoface target.targetRoot.source.base component).outcome_heq _
      (target.oldProjection projection)).trans (target.oldOutcome_heq projection)
  canonical_targetNextVisit_eq := by
    exact target_generated_next (target.targetRoot.withProjectionCoface component)
      (SourceNativeTemporalVisitAt.finite
        ((target.targetRoot.withProjectionCoface component).toAuthoritativeRoot.toRoot.initialVisit))
      target.firstSuccessor
  Answer := target.Answer
  answer := target.answer
  Receipt := target.Receipt
  receipt := target.receipt

variable (optional : Option (SourceNativeProjectionLaw target.targetRoot.source.base.restructuringSource.toLedgerSource))
abbrev optionalTargetCoface : SourceNativeDebtAdmissionActualActionTargetAt sourceRoot sourceVisit sourceEvent sourceEntry sourceAuthority where
  law := target.law
  sourceState := target.sourceState
  stepEvent := target.stepEvent
  sourceSuccessor := target.sourceSuccessor
  TargetV := target.TargetV
  targetRoot := optionalSourceRoot target.targetRoot optional
  initialSupport_eq := target.initialSupport_eq
  initialOldRow := target.initialOldRow
  initialBornRow := target.initialBornRow
  firstSuccessor := target.firstSuccessor
  firstSupport_eq := target.firstSupport_eq
  firstDestination_heq := target.firstDestination_heq
  oldProjection := fun projection => (optionalInstallation target.targetRoot optional).embed (target.oldProjection projection)
  oldProjection_injective := (optionalInstallation target.targetRoot optional).embed_injective.comp target.oldProjection_injective
  oldOutcome_heq := fun projection =>
    ((optionalInstallation target.targetRoot optional).outcome_heq _
      (target.oldProjection projection)).trans (target.oldOutcome_heq projection)
  canonical_targetNextVisit_eq := by
    exact target_generated_next (optionalSourceRoot target.targetRoot optional)
      (SourceNativeTemporalVisitAt.finite
        ((optionalSourceRoot target.targetRoot optional).toAuthoritativeRoot.toRoot.initialVisit))
      target.firstSuccessor
  Answer := target.Answer
  answer := target.answer
  Receipt := target.Receipt
  receipt := target.receipt

end TargetTransport

end SourceOperationInquiry.Context.Faces.Execution.Activation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
