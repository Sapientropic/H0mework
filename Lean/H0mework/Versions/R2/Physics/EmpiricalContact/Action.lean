import H0mework.Versions.R2.Physics.EmpiricalContact.Authority

/-! The actual contact is a conservative action after the preserved physical
history. Its first write computes the new residual on the same live account. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Empirical.ContactEpoch

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open Stage9C.Revision

noncomputable section

def sourceEvent := SpinPair.livingRoot.toAuthoritativeRoot.toLedgerRoot
  |>.generatedAtTemporalVisit sourceVisit

private def occurrencePresentation : ConstructivePresentation
    (SpinPair.livingRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt sourceVisit.current)
    (livingRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt
      livingRoot.toAuthoritativeRoot.toRoot.source.initial) where
  forward := fun _ => emitted .ingress
  backward := fun _ => sourceEvent.occurrence
  backward_forward := fun occurrence => (Recognition.rawOccurrence_eq_generated sourceVisit occurrence).symm
  forward_backward := fun occurrence => (occurrence_unique occurrence).symm

def initialAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt livingRoot initialVisit
    (entry (support .ingress)) :=
  .generatedFromInitialRow livingRoot (entry (support .ingress)) initialEntryRow

def initialAnswerAndNext := livingRoot.generatedCausalEntryAnswerAndNextAt
  initialVisit (entry (support .ingress)) initialAuthority

structure ContactReceiptAt
    (event : ExactTemporalCausalRootEventAt SpinPair.livingRoot.toAuthoritativeRoot.toLedgerRoot sourceVisit)
    (answer : Stage9DEF.Source.OccupiedField) : Type 3 where
  originalEvent : event = sourceEvent
  originalAnswer : answer = (Stage9DEF.Runtime.quantumFace 13).rootRead
  rawContact : (support firstSuccessor.targetCurrent).2 = some releasedContact
  statisticalResidual : (residual (support firstSuccessor.targetCurrent)).2 =
    some (releasedContact, contactResidual releasedContact)
  residualPositive : 0 < contactResidual releasedContact
  demandGenerated : (auditDemand firstSuccessor.targetCurrent).isSome = true
  wholeWrite : HEq initialGenerated.wholeLedgerWriteBack (generatedEvolution initialGenerated.occurrence)
  sameDebt : RootDebtLineageAt N (entry (support .ingress)) (entry (support firstSuccessor.targetCurrent))

private def targetAt
    (event : ExactTemporalCausalRootEventAt SpinPair.livingRoot.toAuthoritativeRoot.toLedgerRoot sourceVisit) :
    SourceNativeSequentialActualActionTargetAt SpinPair.livingRoot sourceVisit event
      sourceEntry sourceAuthority := by
  rw [event.eq_generated]
  exact
    { TargetN := N
      translation := translation
      TargetV := V
      targetRoot := livingRoot
      targetTheory := TheoryState.rootSemantic N
      lawSurface_heq := HEq.rfl
      targetTheory_rootSemantic := ⟨id, fun _ => rfl⟩
      occurrencePresentation := occurrencePresentation
      occurrence_commutes := rfl
      initialSupport_heq := HEq.rfl
      initialOpenLedger := translation.oldOpenLedger (SpinPair.support sourceVisit.current)
      initialOpenLedger_heq := HEq.rfl
      initialLedger_responsibility_commutes := fun candidate => by
        cases materialEntry_unique _ candidate
        rfl
      initialLedger_claim_commutes := fun _ => rfl
      initialLedger_budget_conservative := fun _ => Nat.le_refl _
      initialLedgerNoFresh := fun candidate => ⟨⟨sourceEntry, PLift.up (ingress_no_fresh candidate).symm⟩⟩
      translatedSourceEntryRow := initialEntryRow
      firstSuccessor := firstSuccessor
      canonical_targetNextVisit_eq := rfl
      Answer := Stage9DEF.Source.OccupiedField
      answer := (Stage9DEF.Runtime.quantumFace 13).rootRead
      Receipt := ContactReceiptAt sourceEvent
      receipt :=
        { originalEvent := rfl
          originalAnswer := rfl
          rawContact := first_contact
          statisticalResidual := first_residual
          residualPositive := released_contact_residual_positive
          demandGenerated := first_demand
          wholeWrite := initialGenerated.wholeLedgerWriteBack_eq
          sameDebt := ⟨rfl, account_claim_invariant _ _⟩ } }

def actionProgram : SourceNativeSequentialActualActionProgramAt SpinPair.livingRoot sourceVisit
    sourceEntry sourceAuthority where
  targetAt := targetAt

def generatedAction : SourceGeneratedSequentialActualActionAt actionProgram sourceEvent :=
  actionProgram.generate sourceEvent

def contactReceipt : ContactReceiptAt sourceEvent (Stage9DEF.Runtime.quantumFace 13).rootRead :=
  generatedAction.receipt

theorem action_next : generatedAction.target.targetAnswerAndNext.nextCurrent =
    ⟨V, authoritativeRoot, generatedAction.target.targetVisit⟩ :=
  generatedAction.target.targetAnswerAndNext_next_eq

def inquiryProgram : SourceNativeInquiryCompilationProgramAt SpinPair.livingRoot sourceVisit
    materialU7 materialInquiryCalculus (TheoryState.rootSemantic MaterialN) PUnit.unit
    (ULift.up.{1, 0} (SpinPair.livingRoot.emitted sourceVisit.current))
    sourceEntry sourceAuthority where
  compile := fun event => .actualAction (actionProgram.generate event)

def inquiryState : RootInquiryStateAt MaterialN SpinPair.V where
  root := SpinPair.livingRoot
  visit := sourceVisit
  U7 := materialU7
  calculus := materialInquiryCalculus
  Query := PUnit
  entryAt := fun _ => sourceEntry
  authorityAt := fun _ => sourceAuthority
  compilationProgramAt := fun query => by cases query; exact inquiryProgram
  compilationFaceAt := fun query => by
    cases query
    exact ⟨.quantumCompilation, PUnit.unit, rfl, HEq.rfl⟩
  u7RootDisposition_commutes := by intro query obstruction audit equality; cases query; cases equality

def inquiryPresentation : RootInquiryStatePresentation := ⟨MaterialN, SpinPair.V, .create inquiryState⟩

theorem inquiryPresentation_original_current : inquiryPresentation.erase =
    (Stage9DEF.Runtime.quantumPresentation 12).erase := rfl

end
end SaturationMonoid.PhysicsCore.Stage10.Empirical.ContactEpoch
