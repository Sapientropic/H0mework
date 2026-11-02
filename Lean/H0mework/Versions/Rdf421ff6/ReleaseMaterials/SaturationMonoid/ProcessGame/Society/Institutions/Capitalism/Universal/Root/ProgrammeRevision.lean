import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeLiving
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Compilation

/-! The exact registered Payment failure generates a richer revision whose
first source write enumerates the original finite programme responsibilities.
Every old row survives, the obstruction row has zero continuation credit,
and every instruction child has strictly lower continuation rank than its
parent.  Physical costs use the raw interpreter's separate exact balance. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeRevision

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.TypedSemanticWorldNetworkU8 ConstructiveRoot.RootInquiryCompletion
open ProgrammeWorld ProgrammeSource ProgrammeLedger ProgrammeRestructuring ProgrammeCertification ProgrammeLiving
open M14SourceGeneratedContributionMergeActionSource

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (input : Input Party Good Port Technology Instrument)
  (oldVisit : OldVisit) (sourceIndex boundary : Nat)

abbrev rooted := (FreshPayment.frontier oldVisit sourceIndex boundary).rooted

def initialLedgerRetraction : ConstructiveRetract
    (OpenResponsibilityAt M9ProofCarryingRenewalInquiryRoot.N
      (M9ProofCarryingRenewalInquiryRoot.jointRoot.toAuthoritativeRoot.toRoot.supportAt
        (rooted oldVisit sourceIndex boundary).oldSuccessor.next))
    (OpenResponsibilityAt (N input) .bootstrap) where
  forward := fun _ => inheritedEntry _ (ProgrammeSource.registrationSize input)
  backward := fun _ => ⟨(), ()⟩
  backward_forward := by rintro ⟨row, opened⟩; cases row; cases opened; rfl

def occurrencePresentation : ConstructivePresentation
    (M9ProofCarryingRenewalInquiryRoot.jointRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt
      (rooted oldVisit sourceIndex boundary).oldSuccessor.next)
    ((livingRoot input).toAuthoritativeRoot.toRoot.actual.OccurrenceAt .bootstrap) where
  forward := fun _ => emitted input .bootstrap
  backward := fun _ => M9ProofCarryingRenewalInquiryRoot.jointRoot.emitted
    (rooted oldVisit sourceIndex boundary).oldSuccessor.next
  backward_forward := by
    rintro ⟨support, event⟩
    cases support with
    | false => exact nomatch event
    | true => cases event; rfl
  forward_backward := fun occurrence => (occurrence_eq_emitted input occurrence).symm

def initialGenerated := (livingRoot input).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
  (.finite (livingRoot input).toAuthoritativeRoot.toRoot.initialVisit)

def oldRow : (initialGenerated input).GeneratedEntryRowAt
    (inheritedEntry _ (ProgrammeSource.registrationSize input)) :=
  ((initialGenerated input).canonicalGeneratedEntryRow?
    (inheritedEntry _ (ProgrammeSource.registrationSize input))).get (by rfl)

def obstructionRow : (initialGenerated input).GeneratedEntryRowAt
    (obstructionEntry _ (ProgrammeSource.registrationSize input)) :=
  ((initialGenerated input).canonicalGeneratedEntryRow?
    (obstructionEntry _ (ProgrammeSource.registrationSize input))).get (by rfl)

def generated : GeneratedTypedSemanticWorldNetworkRevisionAt
    (rooted oldVisit sourceIndex boundary) where
  NewN := N input
  translation := ProgrammeWorld.translation _ (ProgrammeSource.registrationSize input)
    (ProgrammeSource.ProgrammeReport Party Good Port Technology Instrument)
    (ProgrammeSource.observation? input)
  NewV := V input
  newLivingRoot := livingRoot input
  new_support_restricts := rfl
  oldTargetOpenLedger := initialLedgerRetraction input oldVisit sourceIndex boundary
  oldTargetOpenClaim_commutes := fun _ => rfl
  oldTargetOpenProgressBudget_not_refilled := fun _ => Nat.le_refl _
  occurrencePresentation := occurrencePresentation input oldVisit sourceIndex boundary
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
  oldEntryRows := fun _ => oldRow input
  newOnlyEntry_hasNoOldPreimage := ⟨by
    rintro ⟨oldEntry, same⟩
    have rows := congrArg Sigma.fst same.down
    change (Row.inherited : Row (ProgrammeSource.registrationSize input)) = .obstruction at rows
    cases rows⟩
  newOnlyEntryRow := obstructionRow input

def firstSuccessor : SourceNativeLedgerGeneratedSuccessorAt
    (generated input oldVisit sourceIndex boundary).initialRestructuringGenerated.occurrence
    (generated input oldVisit sourceIndex boundary).initialRestructuringGenerated.wholeLedgerWriteBack :=
  PUnit.unit

def firstIndex (nonempty : 0 < (ProgrammeSource.registrationSize input)) : Fin (ProgrammeSource.registrationSize input) := ⟨0, nonempty⟩

def genuineSplit (nonempty : 0 < (ProgrammeSource.registrationSize input)) :
    (generated input oldVisit sourceIndex boundary).SourceGeneratedFirstWriteGenuineSplitAt := by
  let left := targetEntry input .bootstrap .inherited
  let right := targetEntry input .bootstrap (.instruction (firstIndex input nonempty))
  have different : left ≠ right := by
    intro same
    have rows := congrArg Sigma.fst same
    change Row.inherited = Row.instruction (firstIndex input nonempty) at rows
    cases rows
  have originSame : ((evolution input .bootstrap).origin left).1 =
      ((evolution input .bootstrap).origin right).1 := rfl
  have child : left.1 ≠ .obstruction := by intro impossible; cases impossible
  refine GeneratedTypedSemanticWorldNetworkRevisionAt.SourceGeneratedFirstWriteGenuineSplitAt.ofCompilerSelectedSplit
    (generated input oldVisit sourceIndex boundary)
    (firstSuccessor input oldVisit sourceIndex boundary) left right different originSame rfl
    (firstSplit input left right originSame child) rfl ?_ ?_
  · intro entry
    rcases bootstrap_no_dormant _ (ProgrammeSource.registrationSize input) entry with inherited | obstruction
    · exact .inl ⟨⟨(rooted oldVisit sourceIndex boundary).oldTargetEntry, ⟨inherited.symm⟩⟩⟩
    · exact .inr obstruction
  · rintro ⟨row, opened⟩
    cases row with
    | inherited => exact .inl ⟨⟨(rooted oldVisit sourceIndex boundary).oldTargetEntry, ⟨rfl⟩⟩⟩
    | instruction _ => exact .inl ⟨⟨(rooted oldVisit sourceIndex boundary).oldTargetEntry, ⟨rfl⟩⟩⟩
    | obstruction => exact .inr rfl

def fieldGrounded (nonempty : 0 < (ProgrammeSource.registrationSize input)) :
    Compilation.Revision oldVisit sourceIndex boundary :=
  FieldGroundedTypedSemanticWorldNetworkRevisionAt.ofSourceGeneratedRestructuring
    (generated input oldVisit sourceIndex boundary)
    ⟨HEq.rfl, ⟨genuineSplit input oldVisit sourceIndex boundary nonempty⟩⟩

theorem first_write_selects_actual_raw_successor :
    (firstSuccessor input oldVisit sourceIndex boundary).targetCurrent = next input .bootstrap := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeRevision
