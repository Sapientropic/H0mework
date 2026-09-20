import H0mework.Physics.RootRuntime.PredictionDimensionlessJoint

/-! The final physical closure has no caller input. The earlier Stage-10
closure remains its historical foundation; Stage 9 supplies the complete
physical theory. The seal recognizes their actual original runtime history. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10

open Stage9C.Revision Recognition Stage9CU.Fields
open StageNineHolonomicField StageNineCClassicalWorldAcceptance
open StageNineEnrichedProofFreeSource

noncomputable section

structure StageTenPhysicalRootClosure where
  private mk ::
  historicalFoundation : StageTenPhysicalRoot.StageTenPhysicalRootClosure
  stageNine : Stage9G.SourceGeneratedContinuousQuantumUnifiedTheoryCredential
  authority : ZeroUnregisteredPhysicalAuthorityReceipt
  sourceExact : Runtime.source = positiveSmoothUnifiedSource
  recoversStageNine : Runtime.configuration = Stage9G.Runtime.configuration
  fullStateReadback : Runtime.configuration = wholeField Runtime.visit.current
  classical : ClassicalWorldAcceptance Runtime.source Runtime.configuration
  activation : Runtime.SameOccurrenceActivation
  nativeInitial : SpinPair.next .ingress = .running SpinPair.initialState
  nativeEvolution : ∀ state : MaterialState,
    wholeField (SpinPair.next (.running state)) =
      Stage9C.Reduction.p286CartanNext positiveSmoothUnifiedSource state.current
        state.smooth state.nondegenerate 0
  completePremiseFold : ∀ left right : SpinPair.Current,
    isRunning left = isRunning right →
    (∀ coordinate point, realCoordinate (wholeField left) coordinate point =
      realCoordinate (wholeField right) coordinate point) →
    left = right ∧ SpinPair.next left = SpinPair.next right ∧
    HEq (SpinPair.generatedEvolution (SpinPair.emitted left))
      (SpinPair.generatedEvolution (SpinPair.emitted right)) ∧
    ∀ projection : SpinPair.Projection,
      HEq (SpinPair.authoritativeRoot.projectionOutcomeAt projection left)
        (SpinPair.authoritativeRoot.projectionOutcomeAt projection right)
  predictionLock : Prediction.JointPrediction

/-- Source-generated total output. Neither an arbitrary actual nor a final
Stage-9 certificate can be passed into this public mouth. -/
def stageTenPhysicalRootClosure : StageTenPhysicalRootClosure := by
  let theory := Stage9G.sourceGeneratedContinuousQuantumUnifiedTheoryCredential
  refine
    { historicalFoundation := StageTenPhysicalRoot.stageTenPhysicalRootClosure
      stageNine := theory
      authority := zeroUnregisteredPhysicalAuthorityReceipt
      sourceExact := Runtime.source_eq
      recoversStageNine := Runtime.recovers_stageNine
      fullStateReadback := rfl
      classical := ?_
      activation := Runtime.sameOccurrenceActivation
      nativeInitial := native_initial_fold
      nativeEvolution := native_running_fold
      completePremiseFold := fun _ _ => completeInput_determines_entireStep
      predictionLock := Prediction.sourceClosedJoint }
  rw [Runtime.source_eq, Runtime.recovers_stageNine, ← Stage9G.Runtime.source_eq]
  exact theory.classical

theorem stageTenPhysicalRootClosed : Nonempty StageTenPhysicalRootClosure :=
  ⟨stageTenPhysicalRootClosure⟩

end
end SaturationMonoid.PhysicsCore.Stage10
