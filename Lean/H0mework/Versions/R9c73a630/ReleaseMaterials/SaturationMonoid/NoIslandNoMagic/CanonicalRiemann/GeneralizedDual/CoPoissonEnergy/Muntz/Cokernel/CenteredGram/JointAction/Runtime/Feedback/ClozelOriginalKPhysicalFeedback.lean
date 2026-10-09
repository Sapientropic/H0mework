import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalAction
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalPricing
import H0mework.Versions.V2.Arithmetic.RiemannBandResponse.Source.Division.Whole
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.UnitResponse.Fourier.Forcing.Pa.Response.Action.SourceModel

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombPhysicalAction
open Complex MeasureTheory Set
open NoIslandNoMagic.CanonicalRiemann
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open scoped InnerProductSpace
noncomputable section
local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (depth : Nat) (half : OriginalKCombCalculation.Half observation)

theorem current_physical : value observation nontrivial depth half ∈
    evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
  have source : value observation nontrivial depth half =
      ((R observation nontrivial half) ^ generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate)
        (burnolPaCombApproximation 0 : BurnolL2) :=
    OriginalKCombCalculation.result_value observation nontrivial half
      (runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence
  rw [source]
  exact CombSource.Division.actual_comb_physical observation nontrivial half.down 0 _ (le_refl _)

attribute [local irreducible] code

theorem born_environment (current : C.Frame) : E.At (Value := C.Value) (Var := C.Var) (sort := ())
    (S.nextBorn current (configuration observation nontrivial half))
    (C.constantEnvironment (physicalProjection
      ((R observation nontrivial half) ((A.epoch current).activeEnvironment () ())))) := by
  intro _ occurrence
  change C.constantEnvironment
    ((I.lowResult (A.epoch current) (lowProgramme observation nontrivial half)
      (S.actualOccurrence current)).2.2.1.1) = _
  have source := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot
      (A.epoch current) (lowProgramme observation nontrivial half)).toAuthoritativeRoot
    (S.datum (A.epoch current) (lowProgramme observation nontrivial half)).reader
    (S.actualOccurrence current)
  change _ = (code observation nontrivial half).eval
    (fun (_ : Unit) (_ : Unit) => ((A.epoch current).activeEnvironment () (), (0 : BurnolL2))) at source
  have computed := source.trans (show (code observation nontrivial half).eval
      (fun (_ : Unit) (_ : Unit) => ((A.epoch current).activeEnvironment () (), (0 : BurnolL2))) =
      (physicalProjection ((R observation nontrivial half) ((A.epoch current).activeEnvironment () ())),
        physicalRemainder ((R observation nontrivial half) ((A.epoch current).activeEnvironment () ()))) from by
        unfold code
        rfl)
  exact congrArg (fun pair : PairValue C.Value () => C.constantEnvironment pair.1) computed

abbrev selected := Complete.atReceipt (configuration observation nontrivial half)
  (initial observation nontrivial depth half) 0

theorem selected_environment : (selected observation nontrivial depth half).activeEnvironment =
    C.nextEnvironment observation nontrivial depth half :=
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix.receipt_environment
    (configuration observation nontrivial half) (initial observation nontrivial depth half)
    (C.initial_environment observation nontrivial depth half) 0).trans
      (E.active (C.initial_environment observation nontrivial depth half))

theorem selected_epoch_environment : (A.epoch (selected observation nontrivial depth half)).activeEnvironment =
    C.nextEnvironment observation nontrivial depth half := by
  have all : E.At (selected observation nontrivial depth half)
      (selected observation nontrivial depth half).activeEnvironment :=
    E.frames_constant (configuration observation nontrivial half)
      (C.initial_environment observation nontrivial depth half)
      (0 + (Complete.receipt (configuration observation nontrivial half)
        (initial observation nontrivial depth half) 0).1)
  exact (E.epoch all).trans (selected_environment observation nontrivial depth half)

theorem actual_physical_next : E.At (Value := C.Value) (Var := C.Var) (sort := ())
    (S.nextBorn (selected observation nontrivial depth half) (configuration observation nontrivial half))
    (C.constantEnvironment (physicalProjection ((R observation nontrivial half)
      (value observation nontrivial depth half)))) := by
  have generated : E.At
      (S.nextBorn (selected observation nontrivial depth half) (configuration observation nontrivial half))
      (C.constantEnvironment (physicalProjection ((R observation nontrivial half)
        ((A.epoch (selected observation nontrivial depth half)).activeEnvironment () ())))) :=
    born_environment observation nontrivial half (selected observation nontrivial depth half)
  intro current occurrence
  have literal := generated (current := current) occurrence
  rw [selected_epoch_environment] at literal
  exact literal

variable (w : ℂ) (wRightQuarter : 1/4 < w.re) (wBelowHalf : w.re < 1/2)

theorem priced_split :
    burnolDivisionNormalizedPhysicalHeatMellin
      (burnolEvenAmbientProjection ((R observation nontrivial half) (value observation nontrivial depth half))) w +
    2 * burnolAmbientCompletedMellinEvaluator
      (burnolDivisionCompletedMellinCoordinate w wRightQuarter wBelowHalf)
      (physicalRemainder ((R observation nontrivial half) (value observation nontrivial depth half))) =
    (-(1 / (observation.coordinate / 2 + w - (1/2 : ℂ)))) *
      burnolDivisionNormalizedPhysicalHeatMellin
        ⟨value observation nontrivial depth half, current_physical observation nontrivial depth half⟩ w := by
  have rq : 1/4 < (observation.coordinate/2).re := by
    rw [Complex.div_re]; norm_num; linarith [half.down]
  exact CombSource.Pricing.original_R_scalar_action (observation.coordinate/2) rq
    ⟨value observation nontrivial depth half, current_physical observation nontrivial depth half⟩
    w wRightQuarter wBelowHalf

-- Raw Model retains the original dual observer; its residual is distinct from the physical orthogonal remainder.
def observer : BurnolL2 →L[ℂ] ℂ × ℂ :=
  (CombSource.originalObserver observation half.down).comp burnolEvenAmbientProjection

theorem model_action : type_of% (SourceGeneratedActionObservationHistory.modelAction_source
    (R observation nontrivial half).toLinearMap (observer observation half).toLinearMap
    (value observation nontrivial depth half)) :=
  SourceGeneratedActionObservationHistory.modelAction_source
    (R observation nontrivial half).toLinearMap (observer observation half).toLinearMap
    (value observation nontrivial depth half)

theorem model_full : type_of% (SourceGeneratedActionObservationHistory.Hilbert.recover_residual
    (R observation nontrivial half) (observer observation half)
    ((R observation nontrivial half) (value observation nontrivial depth half))) :=
  SourceGeneratedActionObservationHistory.Hilbert.recover_residual
    (R observation nontrivial half) (observer observation half)
    ((R observation nontrivial half) (value observation nontrivial depth half))

theorem model_all_future (stage : Nat) : type_of% (SourceGeneratedActionObservationHistory.Hilbert.recover_complete_history
    (R observation nontrivial half) (observer observation half)
    ((R observation nontrivial half) (value observation nontrivial depth half)) stage) :=
  SourceGeneratedActionObservationHistory.Hilbert.recover_complete_history
    (R observation nontrivial half) (observer observation half)
    ((R observation nontrivial half) (value observation nontrivial depth half)) stage

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombPhysicalAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
