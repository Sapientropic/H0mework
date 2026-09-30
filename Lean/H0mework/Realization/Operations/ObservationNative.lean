import H0mework.Realization.Operations.ObservationModel
import H0mework.Realization.Operations.NativeState

/-! The autonomous observation model consumes the original native runtime points and successor. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Observed

open SourceGeneratedActionObservationHistory

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}

theorem sourceAction_pow_point (runtime : LivingRuntimeState process) (stage : Nat) :
    ((sourceAction process) ^ stage) (point runtime) = point (runtime.advance stage) := by
  induction stage with
  | zero => rfl
  | succ stage inductionHypothesis =>
      rw [pow_succ']
      change sourceAction process (((sourceAction process) ^ stage) (point runtime)) =
        point (runtime.advance stage).tick.next
      rw [inductionHypothesis, sourceAction_point]

variable {B : Type u} [AddCommGroup B] (read : process.State → B)

def observedPoint (runtime : LivingRuntimeState process) :
    completion (sourceAction process) (observer process read) :=
  sourceMap (sourceAction process) (observer process read) (point runtime)

theorem observedPoint_read (runtime : LivingRuntimeState process) (bound : Nat) (index : Fin (bound + 1)) :
    stageRead (sourceAction process) (observer process read) bound (observedPoint read runtime) index =
      read (runtime.advance index.val).state := by
  rw [observedPoint, source_reads_stage, sourceAction_pow_point]
  exact observer_point read (runtime.advance index.val)

theorem endomorphism_point (runtime : LivingRuntimeState process) :
    endomorphism (sourceAction process) (observer process read) (observedPoint read runtime) =
      observedPoint read runtime.tick.next := by
  rw [observedPoint, endomorphism_source, sourceAction_point]
  rfl

theorem native_fibre_iff (left right : LivingRuntimeState process) :
    observedPoint read left = observedPoint read right ↔
      ∀ stage : Nat, read (left.advance stage).state = read (right.advance stage).state := by
  rw [observedPoint, observedPoint, source_fibre_iff]
  simp only [sourceAction_pow_point, observer_point]

/-- Point readout and its original occurrence/ledger/next are consumed in one proof. -/
theorem point_factorizes (runtime : LivingRuntimeState process) :
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    endomorphism (sourceAction process) (observer process read) (observedPoint read runtime) =
        observedPoint read stage.next ∧
      read stage.next.state =
        stageRead (sourceAction process) (observer process read) 0
          (observedPoint read stage.next) 0 ∧
      process.stateAt runtime.state = runtime.current ∧
      (process.toAnswerNextCausalWorld.emitted (ULift.up runtime.state) =
          ULift.up stage.activated.generated ∧
        stage.activated.generated.occurrence =
          runtime.current.root.toAuthoritativeRoot.toLedgerRoot.emitted runtime.current.visit.current ∧
        HEq stage.wholeLedgerWriteBack
          (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
        stage.next.current = stage.activated.nextCurrent) := by
  exact ⟨endomorphism_point read runtime, (observedPoint_read read runtime.tick.next 0 0).symm,
    (SourceOperationNative.point_factorizes runtime).2⟩

def modelPoint (runtime : LivingRuntimeState process) : Model (sourceAction process) (observer process read) :=
  projection (sourceAction process) (observer process read) (point runtime)

theorem modelAction_point (runtime : LivingRuntimeState process) :
    modelAction (sourceAction process) (observer process read) (modelPoint read runtime) =
      modelPoint read runtime.tick.next := by
  rw [modelPoint, modelAction_source, sourceAction_point]
  rfl

theorem modelPoint_read (runtime : LivingRuntimeState process) :
    modelReadout (sourceAction process) (observer process read) (modelPoint read runtime) = read runtime.state := by
  rw [modelPoint, modelReadout_projection]
  exact observer_point read runtime

theorem model_native_fibre_iff (left right : LivingRuntimeState process) :
    modelPoint read left = modelPoint read right ↔
      ∀ stage : Nat, read (left.advance stage).state = read (right.advance stage).state := by
  rw [modelPoint, modelPoint, model_fibre_iff]
  simp only [sourceAction_pow_point, observer_point]

theorem model_factorizes (runtime : LivingRuntimeState process) :
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    modelAction (sourceAction process) (observer process read) (modelPoint read runtime) =
        modelPoint read stage.next ∧
      modelReadout (sourceAction process) (observer process read) (modelPoint read stage.next) =
        read stage.next.state ∧
      process.stateAt runtime.state = runtime.current ∧
      (process.toAnswerNextCausalWorld.emitted (ULift.up runtime.state) =
          ULift.up stage.activated.generated ∧
        stage.activated.generated.occurrence =
          runtime.current.root.toAuthoritativeRoot.toLedgerRoot.emitted runtime.current.visit.current ∧
        HEq stage.wholeLedgerWriteBack
          (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
        stage.next.current = stage.activated.nextCurrent) := by
  exact ⟨modelAction_point read runtime, modelPoint_read read runtime.tick.next,
    (SourceOperationNative.point_factorizes runtime).2⟩

end
end SourceOperationNative.Observed
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
