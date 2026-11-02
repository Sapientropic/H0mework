import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeRevision

/-! The same material producer is consumed after a pre-emitter query epoch
extension.  The lower ledger, emitter and history remain the original ones;
only the rooted authority/failure indices are re-exposed at that epoch. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeRevisionCoface

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.ObstructionGeneratedMinimalCoface ConstructiveRoot.TypedSemanticWorldNetworkU8
open ProgrammeWorld ProgrammeSource ProgrammeLedger ProgrammeRestructuring ProgrammeCertification ProgrammeLiving

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (input : Input Party Good Port Technology Instrument)
  (component : SourceNativeProjectionLaw
    M9ProofCarryingRenewalInquiryRoot.jointRoot.toAuthoritativeRoot.toLedgerRoot.source)

abbrev epochRoot := M9ProofCarryingRenewalInquiryRoot.jointRoot.withProjectionCoface component

variable (visit : SourceNativeTemporalVisitAt (epochRoot component).toAuthoritativeRoot.toLedgerRoot)
  (rooted : RootedActualExpressibilityFailureAt (epochRoot component).toAuthoritativeRoot visit
    RootInquiryU8CompletionRegression.U7 RootInquiryU8CompletionRegression.failure)

def oldLedger : ConstructiveRetract
    (OpenResponsibilityAt M9ProofCarryingRenewalInquiryRoot.N
      ((epochRoot component).toAuthoritativeRoot.toRoot.supportAt rooted.oldSuccessor.next))
    (OpenResponsibilityAt (N input) .bootstrap) where
  forward := fun _ => inheritedEntry _ (ProgrammeSource.registrationSize input)
  backward := fun _ => ⟨(), ()⟩
  backward_forward := by rintro ⟨row, opened⟩; cases row; cases opened; rfl

def oldOccurrence : ConstructivePresentation
    ((epochRoot component).toAuthoritativeRoot.toRoot.actual.OccurrenceAt rooted.oldSuccessor.next)
    ((livingRoot input).toAuthoritativeRoot.toRoot.actual.OccurrenceAt .bootstrap) where
  forward := fun _ => emitted input .bootstrap
  backward := fun _ => (epochRoot component).emitted rooted.oldSuccessor.next
  backward_forward := by
    rintro ⟨support, event⟩
    cases support with
    | false => exact nomatch event
    | true => cases event; rfl
  forward_backward := fun occurrence => (occurrence_eq_emitted input occurrence).symm

def generated : GeneratedTypedSemanticWorldNetworkRevisionAt rooted where
  NewN := N input
  translation := ProgrammeWorld.translation _ (ProgrammeSource.registrationSize input)
    (ProgrammeSource.ProgrammeReport Party Good Port Technology Instrument)
    (ProgrammeSource.observation? input)
  NewV := V input
  newLivingRoot := livingRoot input
  new_support_restricts := rfl
  oldTargetOpenLedger := oldLedger input component visit rooted
  oldTargetOpenClaim_commutes := fun _ => rfl
  oldTargetOpenProgressBudget_not_refilled := fun _ => Nat.le_refl _
  occurrencePresentation := oldOccurrence input component visit rooted
  occurrence_commutes := rfl
  firstWrite := PUnit.unit
  newOnlyEntry := obstructionEntry _ (ProgrammeSource.registrationSize input)
  newOnlyProgressBudget_eq_zero := rfl
  revisedClaimHolds := ()
  semanticChange := ()
  revisedClaim_hasNoOldPreimage := ⟨by
    rintro ⟨oldClaim, same⟩
    exact Bool.noConfusion same.down⟩
  newOnlyIncidence_hasNoOldPreimage := ⟨by
    rintro ⟨oldIncidence, same⟩
    exact Bool.noConfusion same.down⟩
  oldEntryRows := fun _ => ProgrammeRevision.oldRow input
  newOnlyEntry_hasNoOldPreimage := ⟨by
    rintro ⟨oldEntry, same⟩
    have rows := congrArg Sigma.fst same.down
    change (Row.inherited : Row (ProgrammeSource.registrationSize input)) = .obstruction at rows
    cases rows⟩
  newOnlyEntryRow := ProgrammeRevision.obstructionRow input

def genuineSplit (nonempty : 0 < (ProgrammeSource.registrationSize input)) :
    (generated input component visit rooted).SourceGeneratedFirstWriteGenuineSplitAt := by
  let left := targetEntry input .bootstrap .inherited
  let right := targetEntry input .bootstrap (.instruction ⟨0, nonempty⟩)
  have different : left ≠ right := by
    intro same
    have rows := congrArg Sigma.fst same
    change Row.inherited = Row.instruction ⟨0, nonempty⟩ at rows
    cases rows
  have sameOrigin : ((evolution input .bootstrap).origin left).1 =
      ((evolution input .bootstrap).origin right).1 := rfl
  have child : left.1 ≠ .obstruction := by intro impossible; cases impossible
  refine GeneratedTypedSemanticWorldNetworkRevisionAt.SourceGeneratedFirstWriteGenuineSplitAt.ofCompilerSelectedSplit
    (generated input component visit rooted) PUnit.unit left right different sameOrigin rfl
    (firstSplit input left right sameOrigin child) rfl ?_ ?_
  · intro entry
    rcases bootstrap_no_dormant _ (ProgrammeSource.registrationSize input) entry with inherited | obstruction
    · exact .inl ⟨⟨rooted.oldTargetEntry, ⟨inherited.symm⟩⟩⟩
    · exact .inr obstruction
  · rintro ⟨row, opened⟩
    cases row with
    | inherited => exact .inl ⟨⟨rooted.oldTargetEntry, ⟨rfl⟩⟩⟩
    | instruction _ => exact .inl ⟨⟨rooted.oldTargetEntry, ⟨rfl⟩⟩⟩
    | obstruction => exact .inr rfl

def fieldGroundedForCoface (nonempty : 0 < (ProgrammeSource.registrationSize input)) :
    FieldGroundedTypedSemanticWorldNetworkRevisionAt rooted :=
  FieldGroundedTypedSemanticWorldNetworkRevisionAt.ofSourceGeneratedRestructuring
    (generated input component visit rooted)
    ⟨HEq.rfl, ⟨genuineSplit input component visit rooted nonempty⟩⟩

theorem revised_source_is_same_literal_programme (nonempty : 0 < (ProgrammeSource.registrationSize input)) :
    (fieldGroundedForCoface input component visit rooted nonempty
      ).generate.newLivingRoot = livingRoot input := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeRevisionCoface
