import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission.SuccessorRead

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open DebtActivationWorld DebtActivationLedger

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (frame : NativeFrame input)
  (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
  (registered : Registration input frame visit.current)

def sourceEntry : OpenResponsibilityAt frame.N
    (frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      (frame.root.emitted visit.current)) := frame.entrySupport _

variable (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt frame.root visit (sourceEntry input frame visit))

def sourceEvent := frame.root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt visit

def sourceSuccessor : SourceNativeLedgerGeneratedSuccessorAt
    (sourceEvent input frame visit).occurrence (sourceEvent input frame visit).wholeLedgerWriteBack := by
  change SourceNativeLedgerGeneratedSuccessorAt (frame.root.emitted visit.current)
    (frame.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current)
  rw [(frame.program.emit visit.current).generated_eq]
  exact PUnit.unit

def initialVisit := SourceNativeTemporalVisitAt.finite
  (livingRoot input frame registered).toAuthoritativeRoot.toRoot.initialVisit

def initialOldRow (entry : OpenResponsibilityAt frame.N
    (frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      (frame.root.emitted visit.current))) :
    ((livingRoot input frame registered).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (initialVisit input frame visit registered)).GeneratedEntryRowAt
        (oldEntry (law := registered.law input frame) (state? := some .pending) entry) :=
  (((livingRoot input frame registered).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
    (initialVisit input frame visit registered)).canonicalGeneratedEntryRow?
      (oldEntry (law := registered.law input frame) (state? := some .pending) entry)).get (by rfl)

def initialBornRow :
    ((livingRoot input frame registered).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (initialVisit input frame visit registered)).GeneratedEntryRowAt
        (debtEntry (N := frame.N) (law := registered.law input frame)
          (supportAt input frame registered (initial input frame registered)).1 .pending) :=
  (((livingRoot input frame registered).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
    (initialVisit input frame visit registered)).canonicalGeneratedEntryRow?
      (debtEntry (N := frame.N) (law := registered.law input frame)
        (supportAt input frame registered (initial input frame registered)).1 .pending)).get (by rfl)

def firstSuccessor : SourceNativeLedgerGeneratedSuccessorAt
    ((livingRoot input frame registered).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (initialVisit input frame visit registered)).occurrence
    ((livingRoot input frame registered).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (initialVisit input frame visit registered)).wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
    ((livingRoot input frame registered).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (initialVisit input frame visit registered)).wholeLedgerWriteBack).get (by rfl)

theorem first_support :
    (source input frame registered).toRootSource.account.supportOf
      (firstSuccessor input frame visit registered).targetOccurrence =
    (frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      (sourceSuccessor input frame visit).targetOccurrence,
      some (registered.firstStep input frame).target) := by
  apply Prod.ext
  · have old := successor_support_eq_of_native _ _ _ _ _ (frame.program.emit visit.current).generated_eq
      (sourceSuccessor input frame visit)
    exact (congrArg frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      (frame.program.emit visit.current).target_emitted).symm.trans old.symm
  · exact congrArg some (next_state input frame registered EventAt.pending)

theorem first_destination :
    HEq (firstSuccessor input frame visit registered).ledgerEvolution.destination
      (jointStepLedgerEvolution (sourceSuccessor input frame visit).ledgerEvolution
        (sourceEntry input frame visit) (registered.firstStep input frame).step).destination := by
  change HEq (patch input frame registered (initial input frame registered)).toLedgerWriteEvolution.destination _
  rw [patch_destination]
  exact (first_destination_is_original_joint_admission input frame registered).trans
    (joint_successor_destination_heq _ _ _ _ _ (frame.program.emit visit.current).generated_eq
      (sourceSuccessor input frame visit) (sourceEntry input frame visit) (registered.firstStep input frame).step).symm

def targetAt (registered : Registration input frame visit.current)
    (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt frame.root visit (sourceEntry input frame visit))
    (event : ExactTemporalCausalRootEventAt frame.root.toAuthoritativeRoot.toLedgerRoot visit) :
    SourceNativeDebtAdmissionActualActionTargetAt frame.root visit event (sourceEntry input frame visit) authority := by
  rw [event.eq_generated]
  exact {
    law := registered.law input frame
    sourceState := .pending
    stepEvent := registered.firstStep input frame
    sourceSuccessor := sourceSuccessor input frame visit
    TargetV := V input frame registered
    targetRoot := livingRoot input frame registered
    initialSupport_eq := rfl
    initialOldRow := initialOldRow input frame visit registered
    initialBornRow := initialBornRow input frame visit registered
    firstSuccessor := firstSuccessor input frame visit registered
    firstSupport_eq := first_support input frame visit registered
    firstDestination_heq := first_destination input frame visit registered
    oldProjection := Sum.inl
    oldProjection_injective := fun _ _ same => Sum.inl.inj same
    oldOutcome_heq := by
      intro projection
      change HEq ((projectionLaw input frame registered).outcomeAt (.inl projection)
        (emitted input frame registered (initial input frame registered)))
        (frame.root.toAuthoritativeRoot.source.projectionLaw.outcomeAt projection (frame.root.emitted visit.current))
      unfold SourceNativeProjectionLaw.outcomeAt
      dsimp only [projectionLaw, classify, initial]
      cases frame.root.toAuthoritativeRoot.source.projectionLaw.classify projection (frame.root.emitted visit.current) <;> rfl
    canonical_targetNextVisit_eq := by
      apply SourceNativeLivingRootClosure.generatedNextCurrentAt_eq_nativeWriteBranch
      rfl
    Answer := Observation input
    answer := observe input (frame.cursor visit.current)
    Receipt := fun answer => ULift.{3, 0} (PLift
      (answer.current = frame.cursor visit.current ∧
        (frame.cursor (firstSuccessor input frame visit registered).targetCurrent.1).account =
          registered.admitted input frame ∧
        total input (admission input registered.claim).residual = registered.claim.quantity ∧
        ¬ Nonempty ((registered.law input frame).SettlementAt (registered.firstStep input frame).target)))
    receipt := ⟨⟨rfl, registered.actual_base_next_account input frame,
      registered.original_principal_survives_registration input frame,
      registered.no_financial_settlement_from_registration input frame⟩⟩ }

def program (registered : Registration input frame visit.current)
    (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt frame.root visit (sourceEntry input frame visit)) :
    SourceNativeDebtAdmissionActualActionProgramAt frame.root visit (sourceEntry input frame visit) authority where
  targetAt := targetAt input frame visit registered authority

def generated := (program input frame visit registered authority).generate (sourceEvent input frame visit)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission
