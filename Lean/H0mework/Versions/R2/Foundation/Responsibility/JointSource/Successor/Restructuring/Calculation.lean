import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Restructuring.Completion

/-! The installed raw fixes a calculation in the existing sealed runtime.
Actual stages consume the complete write and its source certificate. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Successor.Restructuring.Calculation
open SourceOperationEffects SourceOperationExecution RootInquiryCompletion CompilerFromPacketSourceLaw

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : SourceNativeAuthoritativeRootClosure N V)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable {origin : V.Current}
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort) old.toLedgerRoot origin)
variable (packetAt : (current : V.Current) → Packet old.toLedgerRoot current)

def seed := initialRuntime old registered packetAt

def sourceFace : (facade old registered packetAt).FaceAt (seed old registered packetAt) :=
  (rawFace old registered packetAt (seed old registered packetAt)).projection

def sourceRead : Native.Request.Registration.UniformRaw (Value := Value) (Var := Var) (sort := sort) :=
  (rawFace old registered packetAt (seed old registered packetAt)).rootRead

def LocalOperationAt (count : Nat)
    (source : Native.Request.Registration.UniformRaw (Value := Value) (Var := Var) (sort := sort))
    (runtime : Runtime old registered packetAt) (stage : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  remaining (runtimeCurrent old registered packetAt runtime).2.state.1 = remaining source.expression - count ∧
  (runtimeCurrent old registered packetAt runtime).2.state.2.length +
    remaining (runtimeCurrent old registered packetAt runtime).2.state.1 = remaining source.expression ∧
  HEq stage.wholeLedgerWriteBack
    ((compiler registered packetAt).compile (emitted registered packetAt (runtimeCurrent old registered packetAt runtime))) ∧
  (runtimeCurrent old registered packetAt stage.next).2.state =
    mathTarget (runtimeCurrent old registered packetAt runtime).2 ∧
  (tickSuccessor old registered packetAt runtime).ledgerEvolution.destination =
    (whole registered packetAt (runtimeCurrent old registered packetAt runtime)).destination

def frontier : SourceNativeRuntimeCalculationFrontierAt
    (facade old registered packetAt) (seed old registered packetAt) (sourceFace old registered packetAt) :=
  .ofActive PUnit.unit rfl (remaining (sourceRead old registered packetAt).expression)
    (fun count source stage => LocalOperationAt old registered packetAt count.1 source
      ((seed old registered packetAt).advance count.1) stage)

theorem source_payload : (frontier old registered packetAt).sourcePayload = sourceRead old registered packetAt := rfl

theorem realization : SourceNativeRuntimeCalculationRealizationAt (frontier old registered packetAt) where
  operationAt := by
    intro count
    change LocalOperationAt old registered packetAt count.1 (sourceRead old registered packetAt)
      ((seed old registered packetAt).advance count.1) _
    unfold LocalOperationAt
    exact ⟨Completion.budget old registered packetAt count.1,
      Completion.history_accounting old registered packetAt count.1,
      tick_ledger old registered packetAt _, tick_math old registered packetAt _,
      tick_full_destination old registered packetAt _⟩

def normal : SourceGeneratedRuntimeCalculationNormalFormAt (realization old registered packetAt) :=
  .generate (realization old registered packetAt)

def targetRuntime := (normal old registered packetAt).targetRuntime

theorem target_depth : (targetRuntime old registered packetAt).state.down =
    remaining (sourceRead old registered packetAt).expression + 1 :=
  Completion.runtime_depth old registered packetAt _

theorem target_state : (runtimeCurrent old registered packetAt (targetRuntime old registered packetAt)).2.state =
    (Completion.completedEvent old registered packetAt).state :=
  Completion.completed_next_state old registered packetAt

def completed : SourceOperationExecutionDebt.Settlement
    (runtimeCurrent old registered packetAt (targetRuntime old registered packetAt)).2.state :=
  (target_state old registered packetAt).symm ▸ Completion.completed old registered packetAt

theorem completed_value : (completed old registered packetAt).1 =
    (frontier old registered packetAt).sourcePayload.expression.eval
      (frontier old registered packetAt).sourcePayload.environment :=
  SourceOperationExecutionDebt.completed_value _ (completed old registered packetAt)

theorem completed_history :
    (runtimeCurrent old registered packetAt (targetRuntime old registered packetAt)).2.state.2.length =
      remaining (frontier old registered packetAt).sourcePayload.expression := by
  have same := target_state old registered packetAt
  exact (congrArg (fun state : SourceOperationExecutionDebt.State
      registered.input.environment registered.input.expression => state.2.length) same).trans
    (Completion.completed_history_length old registered packetAt)

theorem target_factorizes :
    (process old registered packetAt).toAnswerNextCausalWorld.emitted
      (ULift.up (targetRuntime old registered packetAt).state) =
        ULift.up (targetRuntime old registered packetAt).tick.generated ∧
    (targetRuntime old registered packetAt).tick.generated.occurrence =
      (targetRuntime old registered packetAt).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
        (targetRuntime old registered packetAt).current.visit.current ∧
    HEq (targetRuntime old registered packetAt).tick.generated.wholeLedgerWriteBack
      ((targetRuntime old registered packetAt).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (targetRuntime old registered packetAt).current.visit.current) ∧
    (targetRuntime old registered packetAt).tick.nextCurrent =
      (process old registered packetAt).stateAt
        ((process old registered packetAt).successor (targetRuntime old registered packetAt).state) :=
  (normal old registered packetAt).target_factorizes

end RootGeneratedDebtActivationJointSource.Successor.Restructuring.Calculation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
