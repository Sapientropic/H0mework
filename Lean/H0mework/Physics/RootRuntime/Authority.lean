import H0mework.Physics.RootRuntime.RecognitionWholeCarrier

/-! The current authority seal consumes the historical Stage-10 receipt and
quantifies over every temporal visit and every raw source event. Registration
is the conclusion; the premise contains neither a receipt nor a chosen future. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open Stage9C.Revision Recognition

noncomputable section

structure ZeroUnregisteredPhysicalAuthorityReceipt : Prop where
  private mk ::
  historical : StageTenPhysicalRoot.ZeroUnregisteredPhysicalAuthorityReceipt
  exactOccurrence : ∀ (visit : Visit)
    (occurrence : SpinPair.source.toRootSource.actual.OccurrenceAt visit.current),
    occurrence = (generated visit).occurrence
  wholeLedger : ∀ (visit : Visit)
    (occurrence : SpinPair.source.toRootSource.actual.OccurrenceAt visit.current),
    HEq (generated visit).wholeLedgerWriteBack (SpinPair.generatedEvolution occurrence)
  installedFace : ∀ (visit : Visit)
    (occurrence : SpinPair.source.toRootSource.actual.OccurrenceAt visit.current)
    (projection : SpinPair.Projection),
    HEq (SpinPair.authoritativeRoot.source.projectionLaw.project projection occurrence PUnit.unit)
      (SpinPair.authoritativeRoot.source.projectionLaw.project projection
        (generated visit).occurrence PUnit.unit)
  allAuthority : ∀ (visit : Visit) (projection : SpinPair.Projection),
    HEq ((generated visit).projectionOutcome projection)
      (SpinPair.authoritativeRoot.projectionOutcomeAt projection visit.current)
  next : ∀ visit : Visit,
    (SpinPair.livingRoot.toAuthoritativeRoot.toRoot.evolutionAt visit.current).nextCurrent? =
      some (SpinPair.next visit.current)
  sameRow : ∀ (visit : Visit)
    (occurrence : SpinPair.source.toRootSource.actual.OccurrenceAt visit.current),
    HEq (SpinPair.occurrenceEntry occurrence) (materialEntry (SpinPair.support visit.current))
  residual : ∀ visit : Visit,
    (SpinPair.occurrenceEntry (generated visit).occurrence).1 =
      materialResidual (SpinPair.support visit.current)
  obstructionDemand : ∀ (visit : Visit)
    (obstruction : MaterialN.ObstructionAt (SpinPair.support visit.current)),
    materialU7.generateDemand obstruction = materialEntry (SpinPair.support visit.current)

theorem zeroUnregisteredPhysicalAuthorityReceipt : ZeroUnregisteredPhysicalAuthorityReceipt :=
  { historical := StageTenPhysicalRoot.zeroUnregisteredPhysicalAuthorityReceipt
    exactOccurrence := rawOccurrence_eq_generated
    wholeLedger := rawEvent_wholeLedger
    installedFace := rawEvent_installedFace
    allAuthority := allInstalledAuthority_factorizes
    next := fun _ => rfl
    sameRow := fun _ => rawEvent_sameRow
    residual := fun _ => rfl
    obstructionDemand := fun _ _ => rfl }

/-- The receipt pays both directions: no registered field has an external
event, and no raw event of this fixed source escapes the complete live row. -/
theorem rawPhysicalAuthority_registered (visit : Visit)
    (occurrence : SpinPair.source.toRootSource.actual.OccurrenceAt visit.current)
    (projection : SpinPair.Projection) :
    occurrence = (generated visit).occurrence ∧
    HEq (generated visit).wholeLedgerWriteBack (SpinPair.generatedEvolution occurrence) ∧
    HEq (SpinPair.occurrenceEntry occurrence) (materialEntry (SpinPair.support visit.current)) ∧
    HEq ((generated visit).projectionOutcome projection)
      (SpinPair.authoritativeRoot.projectionOutcomeAt projection visit.current) := by
  let receipt := zeroUnregisteredPhysicalAuthorityReceipt
  exact ⟨receipt.exactOccurrence visit occurrence, receipt.wholeLedger visit occurrence,
    receipt.sameRow visit occurrence, receipt.allAuthority visit projection⟩

end
end SaturationMonoid.PhysicsCore.Stage10
