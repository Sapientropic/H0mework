import H0mework.Fock.HistoryCopy.Field

/-! Every actual past actor supplies the copy material, source law, and same installed native next. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOwnedObservationHistory.NativeCopy.Fock

open SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open ArithmeticGeneration

noncomputable section

def material (depth : Nat) (index : Fin (NativeWindow.bound (runtimeAt depth).current.visit.current + 1)) : Current :=
  NativeWindow.point (runtimeAt depth).current.visit.current index

theorem material_is_unit_iff (depth : Nat)
    (index : Fin (NativeWindow.bound (runtimeAt depth).current.visit.current + 1)) :
    material depth index = CanonicalUnitArithmeticRoot.unitHistory ↔ index.val = 0 := by
  have source := (window_actor_factorizes depth index).1
  constructor
  · intro same
    have atRuntime : ((runtimeAt index.val).current.visit.current : Current) =
        CanonicalUnitArithmeticRoot.unitHistory := source.symm.trans same
    have counts := congrArg UnitHistory.cardinalShadow atRuntime
    change scanIndex (runtimeAt index.val).current.visit.current = 1 at counts
    rw [runtimeAt_scanIndex] at counts
    omega
  · intro zero
    exact source.trans (congrArg (fun position : Nat =>
      ((runtimeAt position).current.visit.current : Current)) zero)

theorem actual_copy_target (depth : Nat)
    (index : Fin (NativeWindow.bound (runtimeAt depth).current.visit.current + 1)) :
    FullMap.map nativeStep (copyStep (material depth index)) (copy (material depth index))
        (fieldAction nativeStep fullRead (fieldPoint nativeStep fullRead (runtimeAt depth).current.visit.current)) =
      fieldPoint (copyStep (material depth index)) sourcePoint
        (copy (material depth index) (runtimePayload depth).nativeWrite.target) := by
  rw [native_field_point (runtimePayload depth)]
  exact FullMap.map_point nativeStep (copyStep (material depth index)) (copy (material depth index))
    ((runtimePayload depth).nativeWrite.target : Current)

theorem runtime_copy_factorizes (depth : Nat)
    (index : Fin (NativeWindow.bound (runtimeAt depth).current.visit.current + 1))
    (value : Field nativeStep fullRead) :
    let runtime := runtimeAt depth
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    let actorStage := (materialHistory depth).stageAt index
    let actor := material depth index
    material depth index = (runtimeAt index.val).current.visit.current ∧
      NativeWindow.imagePoint runtime.current.visit.current index = actorStage.next.current.visit.current ∧
      (fieldAction (copyStep actor) sourcePoint (FullMap.map nativeStep (copyStep actor) (copy actor) value) =
        FullMap.map nativeStep (copyStep actor) (copy actor) (fieldAction nativeStep fullRead value)) ∧
      (FullMap.defect nativeStep nativeStep (copy actor)
          (fieldPoint nativeStep fullRead runtime.current.visit.current) = 0 ↔ index.val = 0) ∧
      FullMap.map nativeStep (copyStep actor) (copy actor)
          (fieldAction nativeStep fullRead (fieldPoint nativeStep fullRead runtime.current.visit.current)) =
        fieldPoint (copyStep actor) sourcePoint (copy actor (runtimePayload depth).nativeWrite.target) ∧
      (runtimePayload depth).sourceOccurrence = runtime.emittedOccurrence ∧
      HEq (runtimeFacade.readoutAt runtime .particleWave)
        (stage.activated.generated.projectionOutcome
          ((runtimeFacade.installationAt runtime .particleWave).embed
            (runtimeFacade.projectionAt runtime .particleWave))) ∧
      (runtimeFacade.process.toAnswerNextCausalWorld.emitted (ULift.up runtime.state) =
          ULift.up stage.activated.generated ∧
        stage.activated.generated.occurrence =
          runtime.current.root.toAuthoritativeRoot.toLedgerRoot.emitted runtime.current.visit.current ∧
        HEq stage.wholeLedgerWriteBack
          (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
        stage.next.current = stage.activated.nextCurrent) ∧
      stage.next.current.visit.current = (runtimePayload depth).nativeWrite.target := by
  have installed := coversAt_factorizes (runtimeAt depth) .particleWave
  exact ⟨(window_actor_factorizes depth index).1, (window_actor_factorizes depth index).2.1,
    generated_action_square (material depth index) value,
    (unit_clock_defect_point_zero_iff (material depth index) _).trans (material_is_unit_iff depth index),
    actual_copy_target depth index, (runtimePayload depth).sourceOccurrence_eq, installed.2.2.2.1,
    (SourceGeneratedRuntimeMaterialStageAt.generate (runtimeAt depth)).factorizes, runtime_current_next depth⟩

end
end SourceOwnedObservationHistory.NativeCopy.Fock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
