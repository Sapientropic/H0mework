import H0mework.Versions.Rc19e94a5.Realization.Operations.Fibre.Recovery
import H0mework.Realization.Operations.FieldInputs
import H0mework.Versions.Rc19e94a5.Arithmetic.FockDynamics.RootRuntime

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceNativeOperationFibreConsumer

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceOperationEffects SourceOperationScalarRelations
open SourceOperationLogic.FibreLift

noncomputable section

abbrev Word := SourceOperationRuntime.FormalCarrier ℤ
  (SourceOperationNative.Field.Value process) (SourceOperationNative.Field.Var process) PUnit.unit

abbrev fieldAt (runtime : LivingRuntimeState process) :=
  SourceOperationRuntime.Fibre.evaluation (R := ℤ) (s := PUnit.unit)
    (SourceOperationNative.statePoint process) (SourceOperationNative.Field.environment process) runtime

abbrev sourceMorphism (runtime : LivingRuntimeState process) :=
  SourceOperationRuntime.Fibre.actualMorphism (R := ℤ) (s := PUnit.unit)
    (SourceOperationNative.statePoint process) (SourceOperationNative.Field.environment process) runtime

theorem runtime_inverse_fibre_action_ledger_next (depth : Nat) (source : Word)
    (target : SourceOperationLogic.Fibre (fieldAt (runtimeAt depth).tick.next)
      (SourceOperationLogic.q (fieldAt (runtimeAt depth).tick.next) source)) :
    let runtime := runtimeAt depth
    let payload := runtimePayload depth
    let point := SourceOperationNative.point (process := process) runtime
    let action : SourceOperationNative.Carrier process →ₗ[ℤ] SourceOperationNative.Carrier process :=
      payload.nativeRuntimeAction
    let environment := SourceOperationNative.Field.environment process
    let residual := liftingResidual (sourceMorphism runtime) source target
    let recovered := SourceOperationRuntime.Fibre.recover (R := ℤ) (s := PUnit.unit)
      (SourceOperationNative.statePoint process) environment runtime residual
    let inventory := updateInventory (R := ℤ) (s := PUnit.unit)
      (environment point) (environment (action point - point)) (target.val - source)
    recovered = inventory ∧
    ((∃ representative : SourceOperationLogic.Fibre (fieldAt runtime)
        (SourceOperationLogic.q (fieldAt runtime) source),
      mapFibre (sourceMorphism runtime) source representative = target) ↔ inventory = 0) ∧
    action point = SourceOperationNative.point (process := process) runtime.tick.next ∧
    payload.nativeWrite = runtime.emittedOccurrence.2.write ∧
    runtimeFacade.readoutAt runtime .particleWave = .inl ⟨runtimeActive depth, payload⟩ ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    runtime.tick.nextCurrent = runtimeFacade.process.stateAt
      (runtimeFacade.process.successor runtime.state) := by
  dsimp only
  have actionPoint : (runtimePayload depth).nativeRuntimeAction
      (SourceOperationNative.point (process := process) (runtimeAt depth)) =
      SourceOperationNative.point (process := process) (runtimeAt depth).tick.next := by
    rw [(runtimePayload depth).nativeRuntimeAction_eq]
    exact SourceOperationNative.sourceAction_point (runtimeAt depth)
  have recovery := SourceOperationRuntime.Fibre.recover_liftingResidual (R := ℤ) (s := PUnit.unit)
    (SourceOperationNative.statePoint process) (SourceOperationNative.Field.environment process)
    (runtimeAt depth) source target
  have first : SourceOperationRuntime.Fibre.firstStage (R := ℤ) (s := PUnit.unit)
      (SourceOperationNative.statePoint process) (SourceOperationNative.Field.environment process)
      (runtimeAt depth) (target.val - source) =
      let acted : SourceOperationNative.Carrier process :=
        (runtimePayload depth).nativeRuntimeAction
          (SourceOperationNative.point (process := process) (runtimeAt depth))
      updateInventory (R := ℤ) (s := PUnit.unit)
        (SourceOperationNative.Field.environment process (SourceOperationNative.point (runtimeAt depth)))
        (SourceOperationNative.Field.environment process
          (acted -
            SourceOperationNative.point (process := process) (runtimeAt depth))) (target.val - source) := by
    dsimp only
    rw [actionPoint]
    rfl
  have recovered := recovery.trans first
  obtain ⟨_, _, ledger, _, next⟩ := coversAt_factorizes (runtimeAt depth) .particleWave
  refine ⟨recovered, ?_, actionPoint, (runtimePayload depth).nativeWrite_source,
    runtimeReadout_is_particleWave depth, ledger, next⟩
  constructor
  · intro lifted
    have zero := (liftingResidual_eq_zero_iff (sourceMorphism (runtimeAt depth)) source target).mpr lifted
    exact recovered.symm.trans ((congrArg
      (SourceOperationRuntime.Fibre.recover (R := ℤ) (s := PUnit.unit)
        (SourceOperationNative.statePoint process) (SourceOperationNative.Field.environment process)
        (runtimeAt depth)) zero).trans (map_zero _))
  · intro zero
    apply (liftingResidual_eq_zero_iff (sourceMorphism (runtimeAt depth)) source target).mp
    apply SourceOperationRuntime.Fibre.recover_injective (R := ℤ) (s := PUnit.unit)
      (SourceOperationNative.statePoint process) (SourceOperationNative.Field.environment process) (runtimeAt depth)
    exact (recovered.trans zero).trans (map_zero _).symm

end
end SourceNativeOperationFibreConsumer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
