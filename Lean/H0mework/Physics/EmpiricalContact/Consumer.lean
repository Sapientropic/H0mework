import H0mework.Physics.EmpiricalContact.Runtime

/-! The new macro occurrence consumes the contact's actual generated audit
claim. Its requested inputs concern the frozen joint apparatus hypothesis. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Empirical.ContactEpoch

open Matrix Bell
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open Stage9C.Revision StageNineEnrichedProofFreeSource ProofFreeRicherAnholonomicSource

noncomputable section

def contactTick := physicalInquiryRuntimeWithContact.tickAt 19
def demandTick := physicalInquiryRuntimeWithContact.tickAt 20

theorem demandTick_answer_present : demandTick.answer.isSome = true := first_demand

def nextObstruction : N.ObstructionAt (support (visit 1).current) :=
  demandTick.answer.get demandTick_answer_present

theorem next_claim : N.obstructionClaim nextObstruction =
    .inr (releasedContact, requiredInputs) := by
  change N.obstructionClaim
    ((auditDemand (.active (SpinPair.next sourceVisit.current) releasedContact)).get _) = _
  simp only [auditDemand, dif_pos released_contact_residual_positive]
  rfl

def next_claim_holds :
    N.HoldsAt (support (visit 1).current) (.inr (releasedContact, requiredInputs)) :=
  PLift.up ⟨rfl, released_contact_residual_positive, rfl⟩

theorem first_field_original : fieldAt firstSuccessor.targetCurrent = Stage9DEF.Source.vector :=
  Stage9DEF.Runtime.fieldAt_eq_vector 13

theorem first_field_nominal_prediction (point : BasePoint) (a b x y : Bool) :
    (Stage9DEF.State.vectorEvaluation
      (right 1 0 *ᵥ (right 0 1 *ᵥ fieldAt firstSuccessor.targetCurrent point))
      (outcomeEffect (nominalAlice a) (nominalBob b) x y).matrix).re =
      nominalPrediction a b x y := by
  rw [first_field_original]
  exact phi_from_fixed_family point (nominalAlice a) (nominalBob b) x y

structure EmpiricalContactClosure : Prop where
  sourcePrediction : DeterministicPreparationPrediction
  nominalTable : ∀ a b x y, nominalPrediction a b x y =
    if (a && !b) = (x != y) then nominalHigh else nominalLow
  originalRuntimeMeasurement : ∀ point a b x y,
    (Stage9DEF.State.vectorEvaluation
      (right 1 0 *ᵥ (right 0 1 *ᵥ Runtime.tick.answer point))
      (outcomeEffect (nominalAlice a) (nominalBob b) x y).matrix).re =
      nominalPrediction a b x y
  exactSourceResidual : 0 < uniformMixtureResidual nominalHigh nominalLow
  frozenNumericalResidual : 0 < contactResidual releasedContact
  originalSeed : physicalInquiryRuntimeWithContact.initialState.engine.node.erase =
    physicalInquiryRuntime.initialState.engine.node.erase
  originalPrefix : ∀ index : Fin 19,
    (physicalInquiryRuntimeWithContact.stateAt index.val).engine.node.erase =
      (physicalInquiryRuntime.stateAt index.val).engine.node.erase
  originalResolutions : ∀ index : Fin 19,
    (physicalInquiryRuntimeWithContact.tickAt index.val).resolutionKind =
      (physicalInquiryRuntime.tickAt index.val).resolutionKind
  originalCompilerImages : ∀ index : Fin 19,
    HEq (physicalInquiryRuntimeWithContact.tickAt index.val).resolution
      (physicalInquiryRuntime.tickAt index.val).resolution
  actionConsumed : contactTick.resolution = .actualAction generatedAction
  actionResumption : SourceNativeInquiryRuntime.SequentialActualActionResumptionAt
    generatedAction physicalInquiryRuntimeWithContact 19
  wholeWrite : HEq initialGenerated.wholeLedgerWriteBack (generatedEvolution initialGenerated.occurrence)
  sameAccount : Nonempty (RootDebtLineageAt N (entry (support .ingress))
    (entry (support firstSuccessor.targetCurrent)))
  computedResidual : (residual (support firstSuccessor.targetCurrent)).2 =
    some (releasedContact, contactResidual releasedContact)
  generatedNext : contactTick.next.node.erase = (readPresentation 1).erase
  demandConsumed : demandTick.resolution = .directlyAnswered (answerFace 1) (answerConsumer 1)
  generatedClaim : N.obstructionClaim nextObstruction = .inr (releasedContact, requiredInputs)
  physicalFieldPreserved : fieldAt firstSuccessor.targetCurrent = Stage9DEF.Source.vector
  requiredIndependentInputs : requiredInputs =
    [.disjointPhaseAlignment, .independentRealBellPreparation, .disjointBinaryReadoutAssignment]

theorem sourceEmpiricalContact : EmpiricalContactClosure where
  sourcePrediction := deterministicPreparationPrediction
  nominalTable := nominalPrediction_value
  originalRuntimeMeasurement := nominal_from_original_runtime
  exactSourceResidual := exact_source_uniform_residual_positive
  frozenNumericalResidual := released_contact_residual_positive
  originalSeed := original_seed
  originalPrefix := original_prefix
  originalResolutions := original_prefix_resolution
  originalCompilerImages := original_prefix_compilation
  actionConsumed := contact_resolution
  actionResumption := contact_installed
  wholeWrite := contactReceipt.wholeWrite
  sameAccount := ⟨contactReceipt.sameDebt⟩
  computedResidual := contactReceipt.statisticalResidual
  generatedNext := contact_next
  demandConsumed := next_consumes_demand
  generatedClaim := next_claim
  physicalFieldPreserved := first_field_original
  requiredIndependentInputs := rfl

end
end SaturationMonoid.PhysicsCore.Stage10.Empirical.ContactEpoch
