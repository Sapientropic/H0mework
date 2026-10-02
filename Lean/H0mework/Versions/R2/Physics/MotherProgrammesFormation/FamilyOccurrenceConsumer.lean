import H0mework.Versions.R2.Physics.SourceFamily.OccurrenceReadout

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFamilyOccurrence

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ProofFreeRicherAnholonomicSource
open Stage9C.Revision StageNineHolonomicField StageNineEnrichedProofFreeSource
open StageNineCClassicalWorldAcceptance StageNineGlobalIntegratedAction
open StageNineDiracDualFormNativeMotherAction SourceFamily

noncomputable section

def successor (visit : MotherVisit) : SourceNativeLedgerGeneratedSuccessorAt
    (Recognition.generated visit).occurrence (Recognition.generated visit).wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
    (Recognition.generated visit).wholeLedgerWriteBack).get (by rfl)

/-- The visit is advanced by the original complete ledger compiler's target. -/
def targetVisit (visit : MotherVisit) : MotherVisit := visit.next (successor visit).next_eq

theorem target_native (visit : MotherVisit) : targetVisit visit = visit.next rfl := rfl

theorem target_patch (visit : MotherVisit) :
    (successor visit).ledgerEvolution =
      (SpinPair.generatedPatch (Recognition.generated visit).occurrence).toLedgerWriteEvolution := rfl

/-- Source material and its full action are calculated along this exact
native edge; the mother's installed projections and ledger retain their payloads. -/
theorem native_formation (visit : MotherVisit) (afterOrigin : originDepth ≤ temporalDepth visit.history)
    (chart : StageNineChart) (point : BasePoint) :
    (successor visit).targetCurrent = (targetVisit visit).current ∧
      (successor visit).ledgerEvolution =
        (SpinPair.generatedPatch (Recognition.generated visit).occurrence).toLedgerWriteEvolution ∧
      SourceNativeTemporalVisitAt.finite (finiteVisit (targetVisit visit)) = targetVisit visit ∧
      formedSource (targetVisit visit) = advanceSource (formedSource visit) ∧
      (formedSource (targetVisit visit)).stageEight.sigmaSeed =
        (formedSource visit).stageEight.sigmaSeed + 1 ∧
      formedField (targetVisit visit) = materialField (advanceSource (formedSource visit)) ∧
      ClassicalWorldAcceptance (formedSource (targetVisit visit)) (formedField (targetVisit visit)) ∧
      formedAction (targetVisit visit) chart point =
        sourceGeneratedDiracDualFormNativeUnifiedLocalDensity (advanceSource (formedSource visit))
          chart point (toContinuumPointField (materialField (advanceSource (formedSource visit))) point) := by
  refine ⟨rfl, target_patch visit, finite_readback _, ?_, ?_, ?_, field_accepted _, ?_⟩
  all_goals rw [target_native]
  · exact formed_next visit afterOrigin
  · exact seed_next visit afterOrigin
  · exact field_next visit afterOrigin
  · exact action_next visit afterOrigin chart point

theorem generated_family_next (step : ℕ) :
    targetVisit (SpinPair.visit (10+step)) = SpinPair.visit (10+(step+1)) ∧
      formedSource (targetVisit (SpinPair.visit (10+step))) = sourceAt (step+1) ∧
      formedField (targetVisit (SpinPair.visit (10+step))) = fieldAt (step+1) := by
  have target : targetVisit (SpinPair.visit (10+step)) = SpinPair.visit (10+(step+1)) := by
    rw [target_native]
    rfl
  exact ⟨target, by rw [target, formed_at], by rw [target, field_at]⟩

theorem generated_family_action (step : ℕ) (chart : StageNineChart) (point : BasePoint) :
    formedAction (SpinPair.visit (10+step)) chart point =
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity (sourceAt step) chart point
        (toContinuumPointField (fieldAt step) point) := by
  rw [formedAction, formed_at, field_at]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFamilyOccurrence
