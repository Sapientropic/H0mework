import H0mework.Versions.Rc19e94a5.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Substitution.Relations
import H0mework.Realization.Logic.SourceScope
import H0mework.Versions.Rc19e94a5.Arithmetic.FockDynamics.RootRuntime

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceNativeSubstitutionConsumer

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceOperationNative SourceOperationRuntime

noncomputable section

abbrev fieldAt (runtime : LivingRuntimeState process) :=
  (completionMap (R := ℤ) (s := PUnit.unit) (statePoint process) (Field.environment process) runtime).hom

theorem runtime_full_substitution_ledger_next (depth : Nat) (word : Substitution.Word process)
    (predicate : Set (SourceOperationLogic.Scope (fieldAt (runtimeAt depth)))) :
    let runtime := runtimeAt depth
    let payload := runtimePayload depth
    let originalAction : Carrier process →ₗ[ℤ] Carrier process := payload.nativeRuntimeAction
    originalAction = sourceAction process ∧
    (∀ bound (index : Fin (bound + 1)),
      stageInventory (R := ℤ) (s := PUnit.unit) (statePoint process) (Field.environment process)
          ((materialHistory runtime bound).stageAt index) (Substitution.words process word) =
        stageInventory (R := ℤ) (s := PUnit.unit) (statePoint process) (Field.environment process)
          ((materialHistory runtime.tick.next bound).stageAt index) word) ∧
    Substitution.action runtime (fieldAt runtime word) = fieldAt runtime (Substitution.words process word) ∧
    Substitution.characterAction runtime
        (Character.sourceMap (R := ℤ) (s := PUnit.unit) (statePoint process) (Field.environment process) runtime word) =
      Character.sourceMap (R := ℤ) (s := PUnit.unit) (statePoint process) (Field.environment process)
        runtime (Substitution.words process word) ∧
    (∀ bound (index : Fin (bound + 1)),
      SourceOperationScalarInventoryLift.liftMap (R := ℤ) (Substitution.words process word) ∈
        LinearMap.range (stageRelationMap (R := ℤ) (s := PUnit.unit) (statePoint process)
          (Field.environment process) ((materialHistory runtime bound).stageAt index)) ↔
      SourceOperationScalarInventoryLift.liftMap (R := ℤ) word ∈
        LinearMap.range (stageRelationMap (R := ℤ) (s := PUnit.unit) (statePoint process)
          (Field.environment process) ((materialHistory runtime.tick.next bound).stageAt index))) ∧
    Set.preimage (Substitution.words process) (SourceOperationLogic.pullback (fieldAt runtime) predicate) =
      SourceOperationLogic.pullback (fieldAt runtime)
        (Set.preimage
          (SourceGeneratedScalarDifferentialResidual.inducedResidualMap (Substitution.differentialMorphism runtime))
          predicate) ∧
    originalAction (point (process := process) runtime) = point (process := process) runtime.tick.next ∧
    payload.nativeWrite = runtime.emittedOccurrence.2.write ∧
    runtimeFacade.readoutAt runtime .particleWave = .inl ⟨runtimeActive depth, payload⟩ ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    runtime.tick.nextCurrent = runtimeFacade.process.stateAt
      (runtimeFacade.process.successor runtime.state) := by
  dsimp only
  have sameAction : ((runtimePayload depth).nativeRuntimeAction : Carrier process →ₗ[ℤ] Carrier process) =
      sourceAction process := (runtimePayload depth).nativeRuntimeAction_eq
  obtain ⟨_, _, ledger, _, next⟩ := coversAt_factorizes (runtimeAt depth) .particleWave
  refine ⟨sameAction, ?_, Substitution.action_source (runtimeAt depth) word,
    Substitution.character_action_source (runtimeAt depth) word, ?_, ?_, ?_,
    (runtimePayload depth).nativeWrite_source, runtimeReadout_is_particleWave depth, ledger, next⟩
  · intro bound index
    exact congrFun (LinearMap.congr_fun (Substitution.prefix_square (runtimeAt depth) bound) word) index
  · intro bound index
    have pair := congrFun (LinearMap.congr_fun (Substitution.prefix_square (runtimeAt depth) bound) word) index
    have current := stage_fibre_generated (R := ℤ) (s := PUnit.unit) (statePoint process)
      (Field.environment process) ((materialHistory (runtimeAt depth) bound).stageAt index)
      (Substitution.words process word) 0
    have nextStage := stage_fibre_generated (R := ℤ) (s := PUnit.unit) (statePoint process)
      (Field.environment process) ((materialHistory (runtimeAt depth).tick.next bound).stageAt index) word 0
    simp only [map_zero, sub_zero] at current nextStage
    exact current.symm.trans ((Eq.to_iff (congrArg (fun value => value = 0) pair)).trans nextStage)
  · exact SourceOperationLogic.pullback_substitution (fieldAt (runtimeAt depth))
      (Substitution.differentialMorphism (runtimeAt depth)) predicate
  · exact (LinearMap.congr_fun sameAction (point (process := process) (runtimeAt depth))).trans
      (sourceAction_point (runtimeAt depth))

end
end SourceNativeSubstitutionConsumer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
