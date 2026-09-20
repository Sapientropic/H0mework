import H0mework.Physics.SpinRuntime.InquiryPrograms

/-! Recognition starts below authority: an event of the original physical
source. Its dependent support already determines the entire occurrence, so
the existing compiler, ledger and every installed face share that occurrence. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Recognition

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open Stage9C.Revision

noncomputable section

abbrev Visit := SourceNativeTemporalVisitAt SpinPair.livingRoot.toAuthoritativeRoot.toLedgerRoot

def generated (visit : Visit) :=
  SpinPair.livingRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit

/-- The input is the lower source event, not an authority certificate. -/
theorem rawOccurrence_eq_emitted {current : SpinPair.Current}
    (occurrence : SpinPair.source.toRootSource.actual.OccurrenceAt current) :
    occurrence = SpinPair.emitted current := by
  rcases occurrence with ⟨targetSupport, event⟩
  change SpinPair.EventAt current targetSupport at event
  cases event.support_eq
  rfl

theorem rawOccurrence_eq_generated (visit : Visit)
    (occurrence : SpinPair.source.toRootSource.actual.OccurrenceAt visit.current) :
    occurrence = (generated visit).occurrence :=
  (rawOccurrence_eq_emitted occurrence).trans (generated visit).occurrence_eq.symm

theorem rawEvent_compiles_native {current : SpinPair.Current}
    (occurrence : SpinPair.source.toRootSource.actual.OccurrenceAt current) :
    SpinPair.source.law.compile occurrence.2 =
      .nativeWrite (materialActionAt (SpinPair.underlying current)) := rfl

theorem rawEvent_wholeLedger (visit : Visit)
    (occurrence : SpinPair.source.toRootSource.actual.OccurrenceAt visit.current) :
    HEq (generated visit).wholeLedgerWriteBack (SpinPair.generatedEvolution occurrence) := by
  cases rawOccurrence_eq_generated visit occurrence
  exact (generated visit).wholeLedgerWriteBack_eq

theorem rawEvent_installedFace (visit : Visit)
    (occurrence : SpinPair.source.toRootSource.actual.OccurrenceAt visit.current)
    (projection : SpinPair.Projection) :
    HEq (SpinPair.authoritativeRoot.source.projectionLaw.project projection occurrence PUnit.unit)
      (SpinPair.authoritativeRoot.source.projectionLaw.project projection
        (generated visit).occurrence PUnit.unit) := by
  cases rawOccurrence_eq_generated visit occurrence
  rfl

theorem allInstalledAuthority_factorizes (visit : Visit) (projection : SpinPair.Projection) :
    HEq ((generated visit).projectionOutcome projection)
      (SpinPair.authoritativeRoot.projectionOutcomeAt projection visit.current) :=
  (generated visit).projectionOutcome_heq_sourceOutcome projection

theorem rawEvent_sameRow {current : SpinPair.Current}
    (occurrence : SpinPair.source.toRootSource.actual.OccurrenceAt current) :
    HEq (SpinPair.occurrenceEntry occurrence) (materialEntry (SpinPair.support current)) := by
  cases rawOccurrence_eq_emitted occurrence
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.Recognition
