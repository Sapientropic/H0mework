import H0mework.Physics.SourceFormation.AuxiliaryFields
import H0mework.Versions.R2.Physics.MotherProgrammesFormationClockBF.Feedback

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.FullAuxiliaryConsumer

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open StageNineHolonomicField StageNineEnrichedProofFreeSource ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeMotherAction StageNineGlobalIntegratedAction
open StageNineFormNativeGaugeWedge StageNineFormNativeGaugeAuxiliaryVariation
open Stage9C.Revision ClockBF ClockBFFeedback FullAuxiliaryFields

noncomputable section

set_option maxHeartbeats 2000000 in
/-- The fixed source-generated family is consumed before and after every
original write. Complete-field coordinates retain the coframe at the same
spacetime argument; the original visit retains event history and the ledger. -/
theorem source_family_consumed (step : ℕ) (chart : StageNineChart) (point : BasePoint) :
    let current := NativeFamily.stateAt sourcePrepared step
    let after := NativeFamily.stateAt sourcePrepared (step + 1)
    let event := NativeFamily.occurrenceAt sourcePrepared step
    let successor := NativeFamily.successorAt sourcePrepared step
    let equivalence := wholeEquiv motherSource
    let beforeData := equivalence current.current
    let afterData := equivalence after.current
    let action := fun field : StageNineHolonomicConfiguration =>
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity motherSource chart point
        (toContinuumPointField field point)
    let generatedAction := fun data : Center motherSource × AuxiliaryField =>
      action data.1.val - (1 / 2 : ℝ) * formNativeP286GaugeWedgeCoefficient (data.2 point)
        (formNativeP286BlockwiseConstitutive (data.1.val.coframe point)
          ((sourceGeneratedUnifiedCouplings motherSource).strongCouplingSquared : ℝ)
          ((sourceGeneratedUnifiedCouplings motherSource).weakCouplingSquared : ℝ)
          ((sourceGeneratedUnifiedCouplings motherSource).hyperchargeCouplingSquared : ℝ) (data.2 point))
    event = SpinPair.emitted (.running current) ∧
    SpinPair.source.toRootSource.actual.compile event =
      .nativeWrite (materialActionAt (SpinPair.underlying (.running current))) ∧
    successor.targetCurrent = (NativeFamily.visitAt sourcePrepared (step + 1)).current ∧
    successor.ledgerEvolution = (SpinPair.generatedPatch event).toLedgerWriteEvolution ∧
    equivalence.symm beforeData = current.current ∧
    equivalence.symm afterData = Recognition.wholeField successor.targetCurrent ∧
    equivalence (equivalence.symm afterData) = afterData ∧
    afterData.1.val.coframe = sourcePrepared.current.coframe ∧
    action current.current = generatedAction beforeData ∧
    action (Recognition.wholeField successor.targetCurrent) = generatedAction afterData := by
  dsimp only
  obtain ⟨compiled, next, _, _⟩ := NativeFamily.next_consumed sourcePrepared step
  have nextField : Recognition.wholeField (NativeFamily.successorAt sourcePrepared step).targetCurrent =
      (NativeFamily.stateAt sourcePrepared (step + 1)).current := by
    rw [next]
    rfl
  have coframe : (NativeFamily.stateAt sourcePrepared (step + 1)).current.coframe =
      sourcePrepared.current.coframe := by
    change (NativeFamily.stateAt (ClockBFPreparation.prepared sourceClockSeed sourceClockSeed_domain)
      (step + 1)).current.coframe =
      (ClockBFPreparation.prepared sourceClockSeed sourceClockSeed_domain).current.coframe
    rw [ClockBFConsumer.generated_coframe, ClockBFPreparation.prepared_current]
  refine ⟨rfl, compiled, next, NativeFamily.complete_patch_consumed sourcePrepared step,
    (wholeEquiv motherSource).symm_apply_apply _, ?_,
    (wholeEquiv motherSource).apply_symm_apply _, ?_, ?_, ?_⟩
  · rw [nextField]
    exact (wholeEquiv motherSource).symm_apply_apply _
  · exact (same_complete_coframe motherSource _).trans coframe
  · exact action_in_generated_fields motherSource chart
      (NativeFamily.stateAt sourcePrepared step).current
      (NativeFamily.stateAt sourcePrepared step).nondegenerate point
  · rw [nextField]
    exact action_in_generated_fields motherSource chart
      (NativeFamily.stateAt sourcePrepared (step + 1)).current
      (NativeFamily.stateAt sourcePrepared (step + 1)).nondegenerate point

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.FullAuxiliaryConsumer
