import H0mework.Realization.Operations.Execution.Relations
import H0mework.Versions.R2.Fock.SourceHistory.Operation.Calculation.Runtime

/-! Paid mathematical history writes its typed boundary back into the
original complete physical pair. A later source update retains its effect. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePhysicalCalculationReceipt

open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceOperationNative
open SourceGeneratedScalarDifferentialResidual
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationPrefix

namespace Joint
export RootGeneratedDebtActivationJointSource.Unit
  (Runtime runtimeCurrent completionRuntime completed completed_source_value)
end Joint

noncomputable section

variable (runtime : LivingRuntimeState process)

def state (canonical : Joint.Runtime (SourcePhysicalCalculationRegistered.registered runtime)) :
    (SourcePhysicalCalculation.calculationLaw runtime).DebtState :=
  (Joint.runtimeCurrent (SourcePhysicalCalculationRegistered.registered runtime) canonical).2.state

def receipt (canonical : Joint.Runtime (SourcePhysicalCalculationRegistered.registered runtime)) :
    RelationIndex ℤ (SourcePhysicalCalculation.rawEnvironment runtime) (Sum.inl OperationSort.parent) →₀ ℤ :=
  (state runtime canonical).2.relationWords

def boundary (canonical : Joint.Runtime (SourcePhysicalCalculationRegistered.registered runtime)) :
    Formal ℤ SourcePhysicalCalculation.CalculationValue SourcePhysicalCalculation.CalculationVar
      (Sum.inl OperationSort.parent) :=
  relationMap (R := ℤ) (SourcePhysicalCalculation.rawEnvironment runtime) (receipt runtime canonical)

def increment : Env SourcePhysicalCalculation.CalculationValue SourcePhysicalCalculation.CalculationVar :=
  SourcePhysicalCalculation.rawEnvironment runtime.tick.next - SourcePhysicalCalculation.rawEnvironment runtime

theorem environment_update :
    SourcePhysicalCalculation.rawEnvironment runtime + increment runtime =
      SourcePhysicalCalculation.rawEnvironment runtime.tick.next := by
  unfold increment
  abel

theorem receipt_boundary (canonical : Joint.Runtime (SourcePhysicalCalculationRegistered.registered runtime)) :
    boundary runtime canonical = Finsupp.single SourcePhysicalCalculation.rawExpression 1 -
      Finsupp.single (state runtime canonical).1 1 :=
  (state runtime canonical).2.relation_boundary

theorem receipt_old (canonical : Joint.Runtime (SourcePhysicalCalculationRegistered.registered runtime)) :
    evaluation (R := ℤ) (s := Sum.inl OperationSort.parent)
      (SourcePhysicalCalculation.rawEnvironment runtime) (boundary runtime canonical) = 0 :=
  (state runtime canonical).2.relation_old

theorem paid_pair (canonical : Joint.Runtime (SourcePhysicalCalculationRegistered.registered runtime)) :
    (state runtime canonical).1.eval (SourcePhysicalCalculation.rawEnvironment runtime) =
      ((payloadAt runtime).sourceState, (payloadAt runtime).forcedTrace) :=
  (state runtime canonical).2.sound.symm.trans (SourcePhysicalCalculation.raw_value runtime)

theorem future_boundary (canonical : Joint.Runtime (SourcePhysicalCalculationRegistered.registered runtime)) :
    evaluation (R := ℤ) (s := Sum.inl OperationSort.parent)
      (SourcePhysicalCalculation.rawEnvironment runtime.tick.next) (boundary runtime canonical) =
      ((payloadAt runtime.tick.next).sourceState, (payloadAt runtime.tick.next).forcedTrace) -
        (state runtime canonical).1.eval (SourcePhysicalCalculation.rawEnvironment runtime.tick.next) := by
  rw [receipt_boundary, map_sub]
  simp only [evaluation, Finsupp.linearCombination_single, one_smul]
  exact congrArg (fun value => value -
    (state runtime canonical).1.eval (SourcePhysicalCalculation.rawEnvironment runtime.tick.next))
      (SourcePhysicalCalculation.raw_value runtime.tick.next)

theorem receipt_effect (canonical : Joint.Runtime (SourcePhysicalCalculationRegistered.registered runtime)) :
    effectEvaluator (R := ℤ) (s := Sum.inl OperationSort.parent)
      (SourcePhysicalCalculation.rawEnvironment runtime) (increment runtime)
        (boundary runtime canonical) =
      ((payloadAt runtime.tick.next).sourceState, (payloadAt runtime.tick.next).forcedTrace) -
        (state runtime canonical).1.eval (SourcePhysicalCalculation.rawEnvironment runtime.tick.next) := by
  have updated := LinearMap.congr_fun (evaluation_update
    (SourcePhysicalCalculation.rawEnvironment runtime) (increment runtime)) (boundary runtime canonical)
  rw [environment_update, LinearMap.add_apply, receipt_old, zero_add] at updated
  exact updated.symm.trans (future_boundary runtime canonical)

theorem receipt_inventory (canonical : Joint.Runtime (SourcePhysicalCalculationRegistered.registered runtime)) :
    updateInventory (R := ℤ) (SourcePhysicalCalculation.rawEnvironment runtime) (increment runtime)
        (boundary runtime canonical) =
      (0, ((payloadAt runtime.tick.next).sourceState, (payloadAt runtime.tick.next).forcedTrace) -
        (state runtime canonical).1.eval (SourcePhysicalCalculation.rawEnvironment runtime.tick.next)) := by
  exact ((state runtime canonical).2.relation_inventory (increment runtime)).trans
    (congrArg (fun effect => (0, effect)) (receipt_effect runtime canonical))

theorem receipt_residual (canonical : Joint.Runtime (SourcePhysicalCalculationRegistered.registered runtime)) :
    (residualEquivRange (evaluation (R := ℤ) (SourcePhysicalCalculation.rawEnvironment runtime.tick.next))
      (canonicalResidual (evaluation (R := ℤ) (SourcePhysicalCalculation.rawEnvironment runtime.tick.next))
        (boundary runtime canonical))).val =
      ((payloadAt runtime.tick.next).sourceState, (payloadAt runtime.tick.next).forcedTrace) -
        (state runtime canonical).1.eval (SourcePhysicalCalculation.rawEnvironment runtime.tick.next) := by
  have generated := (state runtime canonical).2.updated_residual (R := ℤ) (increment runtime)
  rw [environment_update] at generated
  exact generated.trans (receipt_effect runtime canonical)

theorem receipt_residual_zero_iff
    (canonical : Joint.Runtime (SourcePhysicalCalculationRegistered.registered runtime)) :
    canonicalResidual (evaluation (R := ℤ) (SourcePhysicalCalculation.rawEnvironment runtime.tick.next))
        (boundary runtime canonical) = 0 ↔
      ((payloadAt runtime.tick.next).sourceState, (payloadAt runtime.tick.next).forcedTrace) -
        (state runtime canonical).1.eval (SourcePhysicalCalculation.rawEnvironment runtime.tick.next) = 0 := by
  rw [canonicalResidual_eq_zero_iff, future_boundary]

theorem receipt_cochain (canonical : Joint.Runtime (SourcePhysicalCalculationRegistered.registered runtime)) :
    SourceOperationScalarCochain.boundary (R := ℤ) (boundary runtime canonical) ∈
      LinearMap.range (relationMap (R := ℤ)
        (mixedEnvironment (SourcePhysicalCalculation.rawEnvironment runtime) (increment runtime))) :=
  (state runtime canonical).2.relation_cochain (increment runtime)

theorem completed_receipt_residual
    (canonical : Joint.Runtime (SourcePhysicalCalculationRegistered.registered runtime)) :
    (residualEquivRange (evaluation (R := ℤ) (SourcePhysicalCalculation.rawEnvironment runtime.tick.next))
      (canonicalResidual (evaluation (R := ℤ) (SourcePhysicalCalculation.rawEnvironment runtime.tick.next))
        (boundary runtime (Joint.completionRuntime
          (SourcePhysicalCalculationRegistered.registered runtime) canonical)))).val =
      ((payloadAt runtime.tick.next).sourceState, (payloadAt runtime.tick.next).forcedTrace) -
        ((payloadAt runtime).sourceState, (payloadAt runtime).forcedTrace) := by
  let settled := Joint.completed (SourcePhysicalCalculationRegistered.registered runtime) canonical
  have sourceValue : settled.1 = ((payloadAt runtime).sourceState, (payloadAt runtime).forcedTrace) :=
    (Joint.completed_source_value (SourcePhysicalCalculationRegistered.registered runtime) canonical).trans
      (SourcePhysicalCalculation.raw_value runtime)
  have futureRead : (state runtime (Joint.completionRuntime
      (SourcePhysicalCalculationRegistered.registered runtime) canonical)).1.eval
      (SourcePhysicalCalculation.rawEnvironment runtime.tick.next) =
        ((payloadAt runtime).sourceState, (payloadAt runtime).forcedTrace) :=
    (congrArg (fun expression => expression.eval (SourcePhysicalCalculation.rawEnvironment runtime.tick.next))
      settled.2.down).trans sourceValue
  exact (receipt_residual runtime (Joint.completionRuntime
    (SourcePhysicalCalculationRegistered.registered runtime) canonical)).trans
      (congrArg (fun value =>
        ((payloadAt runtime.tick.next).sourceState, (payloadAt runtime.tick.next).forcedTrace) - value) futureRead)

theorem completed_receipt_residual_zero_iff
    (canonical : Joint.Runtime (SourcePhysicalCalculationRegistered.registered runtime)) :
    canonicalResidual (evaluation (R := ℤ) (SourcePhysicalCalculation.rawEnvironment runtime.tick.next))
        (boundary runtime (Joint.completionRuntime
          (SourcePhysicalCalculationRegistered.registered runtime) canonical)) = 0 ↔
      ((payloadAt runtime.tick.next).sourceState, (payloadAt runtime.tick.next).forcedTrace) =
        ((payloadAt runtime).sourceState, (payloadAt runtime).forcedTrace) := by
  rw [← LinearEquiv.map_eq_zero_iff
    (residualEquivRange (evaluation (R := ℤ) (SourcePhysicalCalculation.rawEnvironment runtime.tick.next)))]
  rw [Subtype.ext_iff]
  change (residualEquivRange (evaluation (R := ℤ) (SourcePhysicalCalculation.rawEnvironment runtime.tick.next))
    (canonicalResidual (evaluation (R := ℤ) (SourcePhysicalCalculation.rawEnvironment runtime.tick.next))
      (boundary runtime (Joint.completionRuntime
        (SourcePhysicalCalculationRegistered.registered runtime) canonical)))).val = 0 ↔ _
  rw [completed_receipt_residual, sub_eq_zero]

theorem paid_pair_inverse (canonical : Joint.Runtime (SourcePhysicalCalculationRegistered.registered runtime))
    (alternative : ParentCarrier) :
    let seen := (state runtime canonical).1.eval (SourcePhysicalCalculation.rawEnvironment runtime)
    seen = ((payloadAt runtime).sourceState, (payloadAt runtime).forcedTrace) ∧
      (jointMeasurement alternative = jointMeasurement (payloadAt runtime).targetState ↔
        alternative - (seen.1 + seen.2) ∈ JointMeasurementKernel) := by
  dsimp only
  refine ⟨paid_pair runtime canonical, ?_⟩
  rw [paid_pair]
  rw [← NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationCochain.stage_state_from_boundary
    (SourceGeneratedRuntimeMaterialStageAt.generate runtime)]
  exact (payloadAt runtime).inverseFibreLaw alternative

end
end SourcePhysicalCalculationReceipt
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
