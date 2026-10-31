import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.External.ClaimsReceipt.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Living
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Inquiry.State

/-! The first accounting source enters through the existing no-fresh actual
action.  Its first write performs the old source's current body once and
retains every already occurred item for native registration. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Ingress

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth : Nat)

def identityTranslation (N : WorldRelationNetwork) : TypedSemanticWorldNetworkTranslationAt N N where
  support := ⟨id, id, fun _ => rfl⟩
  anchor := ⟨id, id, fun _ => rfl⟩
  incidence := ⟨id, id, fun _ => rfl⟩
  lineage := ⟨id, id, fun _ => rfl⟩
  responsibility := ⟨id, id, fun _ => rfl⟩
  claim := ⟨id, id, fun _ => rfl⟩
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun _ => rfl
  lineage_commutes := fun _ => rfl
  oldOpenLedger := fun _ => ⟨id, id, fun _ => rfl⟩
  oldOpenClaim_commutes := fun _ _ => rfl
  oldOpenProgressBudget_commutes := fun _ _ => rfl
  oldHoldsSurvives := fun _ _ proof => proof
  oldDispositionSurvives := fun _ _ proof => proof

def start : Cursor.State input := Cursor.enteringAt input (depth + 1)

theorem start_positive : 0 < Cursor.physicalVisitIndex input (start input depth) :=
  Nat.zero_lt_succ depth

def targetRoot := AccountSource.livingRoot input (start input depth) (start_positive input depth)

def sourceRoot := ProgrammeLiving.livingRoot input
def sourceVisit := ProgrammeHistory.temporalVisit input (depth + 1)
def sourceEntry := ProgrammeLiving.inquiryEntryAt input
  (ProgrammeSource.emitted input (ProgrammeHistory.visitAt input (depth + 1)).current)
def sourceAuthority := ProgrammeInquiry.authorityAt input (depth + 1)

def targetInitial := (targetRoot input depth).toAuthoritativeRoot.toRoot.initialVisit

def occurrencePresentation : ConstructivePresentation
    ((sourceRoot input).toAuthoritativeRoot.toRoot.actual.OccurrenceAt (sourceVisit input depth).current)
    ((targetRoot input depth).toAuthoritativeRoot.toRoot.actual.OccurrenceAt (targetInitial input depth).current) where
  forward := fun _ => (targetRoot input depth).emitted (targetInitial input depth).current
  backward := fun _ => (sourceRoot input).emitted (sourceVisit input depth).current
  backward_forward := fun occurrence => (ProgrammeSource.occurrence_eq_emitted input occurrence).symm
  forward_backward := fun occurrence =>
    (AccountSource.occurrence_eq_emitted input (start input depth) (start_positive input depth) occurrence).symm

def initialRow :
    ((targetRoot input depth).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite (targetInitial input depth))).GeneratedEntryRowAt (sourceEntry input depth) :=
  (((targetRoot input depth).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
    (.finite (targetInitial input depth))).canonicalGeneratedEntryRow? (sourceEntry input depth)).get (by rfl)

def firstSuccessor : SourceNativeLedgerGeneratedSuccessorAt
    ((targetRoot input depth).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite (targetInitial input depth))).occurrence
    ((targetRoot input depth).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite (targetInitial input depth))).wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
    ((targetRoot input depth).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite (targetInitial input depth))).wholeLedgerWriteBack).get (by rfl)

theorem first_write_has_the_original_material_target :
    AccountSource.materialAt input (start input depth) (firstSuccessor input depth).targetCurrent =
      (ProgrammeLiving.executionFace input
        (ProgrammeSource.emitted input (ProgrammeHistory.visitAt input (depth + 1)).current)).after :=
  AccountSource.actual_fresh_body_is_the_original_raw_next input (start input depth)
    (AccountSource.initial input (start input depth) (start_positive input depth)) (Or.inl rfl)

def targetAt (event : ExactTemporalCausalRootEventAt
    (sourceRoot input).toAuthoritativeRoot.toLedgerRoot (sourceVisit input depth)) :
    SourceNativeSequentialActualActionTargetAt (sourceRoot input) (sourceVisit input depth)
      event (sourceEntry input depth) (sourceAuthority input depth) := by
  rw [event.eq_generated]
  exact {
    TargetN := ProgrammeSource.N input
    translation := identityTranslation (ProgrammeSource.N input)
    TargetV := AccountSource.V input (start input depth)
    targetRoot := targetRoot input depth
    targetTheory := TheoryState.rootSemantic (ProgrammeSource.N input)
    lawSurface_heq := HEq.rfl
    targetTheory_rootSemantic := ⟨id, fun _ => rfl⟩
    occurrencePresentation := occurrencePresentation input depth
    occurrence_commutes := rfl
    initialSupport_heq := HEq.rfl
    initialOpenLedger := (identityTranslation (ProgrammeSource.N input)).oldOpenLedger
      (ProgrammeSource.supportAt input (ProgrammeHistory.visitAt input (depth + 1)).current)
    initialOpenLedger_heq := HEq.rfl
    initialLedger_responsibility_commutes := fun _ => rfl
    initialLedger_claim_commutes := fun _ => rfl
    initialLedger_budget_conservative := fun _ => Nat.le_refl _
    initialLedgerNoFresh := fun entry => ⟨⟨entry, ⟨rfl⟩⟩⟩
    translatedSourceEntryRow := initialRow input depth
    firstSuccessor := firstSuccessor input depth
    canonical_targetNextVisit_eq := by
      apply SourceNativeLivingRootClosure.generatedNextCurrentAt_eq_nativeWriteBranch
      rfl
    Answer := ProgrammeLiving.ExecutionFaceAt input
      (ProgrammeSource.emitted input (ProgrammeHistory.visitAt input (depth + 1)).current)
    answer := ProgrammeLiving.executionFace input
      (ProgrammeSource.emitted input (ProgrammeHistory.visitAt input (depth + 1)).current)
    Receipt := fun answer => ULift.{3, 0} (PLift
      (AccountSource.materialAt input (start input depth) (firstSuccessor input depth).targetCurrent = answer.after)) ×
        ULift.{3, 0} (Abolition.Completion.Actual.External.Admission.InitialClaimsDecision input)
    receipt := ⟨⟨⟨first_write_has_the_original_material_target input depth⟩⟩,
      ⟨Abolition.Completion.Actual.External.Admission.inspectInitialClaims input⟩⟩ }

def program : SourceNativeSequentialActualActionProgramAt
    (sourceRoot input) (sourceVisit input depth) (sourceEntry input depth) (sourceAuthority input depth) where
  targetAt := targetAt input depth

def sourceEvent := (sourceRoot input).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt (sourceVisit input depth)

def generated := (program input depth).generate (sourceEvent input depth)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Ingress
