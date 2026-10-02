import H0mework.Versions.R2.Foundation.Responsibility.JointSource.OwnerFree.Completion

/-! The actual source raw sets the existing runtime frontier. Every stage
pays through its original tick and complete whole-ledger material. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.OwnerFree.Calculation
open SourceOperationEffects SourceOperationExecution RootInquiryCompletion
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : SourceNativeAuthoritativeRootClosure N V) (origin : V.Current)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (reader : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin →
  Raw (Value := Value) (Var := Var) (sort := sort))

def seed := initialRuntime old origin reader

def sourceFace : (facade old origin reader).FaceAt (seed old origin reader) :=
  (rawFace old origin reader (seed old origin reader)).projection

def sourceRead : Raw (Value := Value) (Var := Var) (sort := sort) :=
  (rawFace old origin reader (seed old origin reader)).rootRead

def LocalOperationAt (count : Nat) (source : Raw (Value := Value) (Var := Var) (sort := sort))
    (runtime : Runtime old origin reader) (stage : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  remaining (runtimeCurrent old origin reader runtime).1 = remaining source.expression - count ∧
  (runtimeCurrent old origin reader runtime).2.length + remaining (runtimeCurrent old origin reader runtime).1 =
    remaining source.expression ∧
  stage.activated.generated.occurrence = runtime.current.root.toAuthoritativeRoot.toLedgerRoot.emitted runtime.current.visit.current ∧
  HEq stage.wholeLedgerWriteBack (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
    runtime.current.visit.current) ∧
  runtimeCurrent old origin reader stage.next = nextState old origin reader (runtimeCurrent old origin reader runtime)

def frontier : SourceNativeRuntimeCalculationFrontierAt
    (facade old origin reader) (seed old origin reader) (sourceFace old origin reader) :=
  .ofActive PUnit.unit rfl (remaining (sourceRead old origin reader).expression)
    (fun count source stage => LocalOperationAt old origin reader count.1 source
      ((seed old origin reader).advance count.1) stage)

theorem source_payload : (frontier old origin reader).sourcePayload = sourceRead old origin reader := rfl

theorem realization : SourceNativeRuntimeCalculationRealizationAt (frontier old origin reader) where
  operationAt := by
    intro count
    change LocalOperationAt old origin reader count.1 (sourceRead old origin reader)
      ((seed old origin reader).advance count.1) _
    unfold LocalOperationAt
    exact ⟨Completion.budget old origin reader count.1,
      Completion.history_accounting old origin reader count.1,
      rfl,
      (SourceGeneratedRuntimeMaterialStageAt.generate ((seed old origin reader).advance count.1)).factorizes.2.2.1,
      tick_math old origin reader _⟩

def normal : SourceGeneratedRuntimeCalculationNormalFormAt (realization old origin reader) :=
  .generate (realization old origin reader)

def targetRuntime := (normal old origin reader).targetRuntime

theorem target_depth : (targetRuntime old origin reader).state.down =
    remaining (sourceRead old origin reader).expression + 1 :=
  Completion.runtime_depth old origin reader _

theorem target_state : runtimeCurrent old origin reader (targetRuntime old origin reader) =
    Completion.completedState old origin reader := Completion.completed_next_state old origin reader

def completed : SourceOperationExecutionDebt.Settlement (runtimeCurrent old origin reader (targetRuntime old origin reader)) :=
  (target_state old origin reader).symm ▸ Completion.completed old origin reader

theorem completed_value : (completed old origin reader).1 =
    (frontier old origin reader).sourcePayload.expression.eval (frontier old origin reader).sourcePayload.environment :=
  SourceOperationExecutionDebt.completed_value _ (completed old origin reader)

theorem completed_history : (runtimeCurrent old origin reader (targetRuntime old origin reader)).2.length =
    remaining (frontier old origin reader).sourcePayload.expression :=
  (congrArg (fun state : Current old origin reader => state.2.length) (target_state old origin reader)).trans
    (Completion.completed_history_length old origin reader)

theorem target_factorizes :
    (process old origin reader).toAnswerNextCausalWorld.emitted (ULift.up (targetRuntime old origin reader).state) =
      ULift.up (targetRuntime old origin reader).tick.generated ∧
    (targetRuntime old origin reader).tick.generated.occurrence =
      (targetRuntime old origin reader).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
        (targetRuntime old origin reader).current.visit.current ∧
    HEq (targetRuntime old origin reader).tick.generated.wholeLedgerWriteBack
      ((targetRuntime old origin reader).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (targetRuntime old origin reader).current.visit.current) ∧
    (targetRuntime old origin reader).tick.nextCurrent =
      (process old origin reader).stateAt ((process old origin reader).successor (targetRuntime old origin reader).state) :=
  (normal old origin reader).target_factorizes

end RootGeneratedDebtActivationJointSource.OwnerFree.Calculation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
