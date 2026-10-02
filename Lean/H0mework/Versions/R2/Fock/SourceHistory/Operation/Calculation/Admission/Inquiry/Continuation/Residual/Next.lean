import H0mework.Versions.R2.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Continuation.ResidualRuntime
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Request.Residual.Runtime

/-! Every actual residual-current retains the original Fock actor and source
projection. Its next residual reads that actor's actual contextual action,
then reuses the generic birth and runtime without a handwritten epoch. -/

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePhysicalCalculationAdmission.Inquiry.Continuation.Residual.Next
open SourceOperationEffects SourceOperationExecution SourceOperationNative
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationPrefix
namespace R
export RootGeneratedDebtActivationJointSource.Native.Request
  (finiteVisit mathCurrent mathState mathEntry targetRoot nextProgram nextScope)
end R
namespace Generic
export RootGeneratedDebtActivationJointSource.Native.Request.Residual
  (Occurrence nextRegistered material actualMaterial environment_actual history_actual
    budget residual_actual inquiry actual_node initial_kind completed completed_value)
end Generic
noncomputable section
variable (runtime : LivingRuntimeState process) (depth : Nat)
abbrev old := ResidualAdmission.oldState runtime depth
abbrev request := ResidualAdmission.request runtime depth

theorem finite_original (count : Nat) :
  (R.finiteVisit (old runtime depth) (program runtime) (request runtime depth) (identityScope runtime) count).current.1 =
    SourcePhysicalCalculationAdmission.Inquiry.mathCurrent runtime (depth + count) := by
  induction count with
  | zero => rfl
  | succ count prior =>
      change (RootGeneratedDebtActivationJointSource.Unit.JointV
        (SourcePhysicalCalculationAdmission.registered runtime)).nativeTarget
          ((program runtime).emit
            (R.finiteVisit (old runtime depth) (program runtime) (request runtime depth) (identityScope runtime) count).current.1).write = _
      rw [prior]
      rfl

variable (count : Nat)

theorem math_original : (R.mathCurrent (old runtime depth) (program runtime) (request runtime depth)
    (identityScope runtime) count).1 = SourcePhysicalCalculationAdmission.Inquiry.mathCurrent runtime (depth + (count + 1)) :=
  finite_original runtime depth (count + 1)

theorem source_original : (R.mathCurrent (old runtime depth) (program runtime) (request runtime depth)
    (identityScope runtime) count).1.1 =
      SourcePhysicalCalculation.baseCurrent (runtime.advance (depth + (count + 1) + 1)) :=
  (congrArg (fun current => current.1) (math_original runtime depth count)).trans
    (SourcePhysicalCalculationAdmission.Inquiry.Consumer.current_original runtime (depth + (count + 1)))

abbrev currentState := R.mathState (old runtime depth) (program runtime) (request runtime depth)
  (identityScope runtime) count

def originalOccurrence
    (source : Generic.Occurrence (old runtime depth) (program runtime) (request runtime depth)
      (identityScope runtime) count) :=
  Joint.originalOccurrence (SourcePhysicalCalculationAdmission.registered runtime)
    (RootGeneratedDebtActivationJointSource.Native.originalOccurrence
      (program runtime) (request runtime depth) source)

def physicalActive
    (source : Generic.Occurrence (old runtime depth) (program runtime) (request runtime depth)
      (identityScope runtime) count) :
    projectionLaw.ActiveAt PUnit.unit (originalOccurrence runtime depth count source) :=
  ⟨by
    change 1 ≤ scanIndex (R.mathCurrent (old runtime depth) (program runtime) (request runtime depth)
      (identityScope runtime) count).1.1
    exact (congrArg scanIndex (source_original runtime depth count)).symm ▸
      (activeAt (runtime.advance (depth + (count + 1) + 1))).down⟩

def physicalPayload
    (source : Generic.Occurrence (old runtime depth) (program runtime) (request runtime depth)
      (identityScope runtime) count) :=
  projectionLaw.project PUnit.unit (originalOccurrence runtime depth count source)
    (physicalActive runtime depth count source)

def actionEnvironment
    (_source : Generic.Occurrence (old runtime depth) (program runtime) (request runtime depth)
      (identityScope runtime) count) :
    Env SourcePhysicalCalculation.CalculationValue SourcePhysicalCalculation.CalculationVar :=
  Context.environment (PhysicalValue := SourceOperationInventoryLift.PairValue OperationValue)
    (statePoint process (scanIndex (R.mathCurrent (old runtime depth) (program runtime) (request runtime depth)
      (identityScope runtime) count).1.1 - 1))

private theorem actualScan (actual : LivingRuntimeState process) :
    scanIndex (SourcePhysicalCalculation.baseCurrent actual) = actual.state + 1 := by
  change scanIndex (NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime.finiteVisit actual.state).current = _
  rw [finiteVisit_current]
  exact ArithmeticGeneration.UnitHistory.cardinalShadow_generate _

theorem action_environment_actual
    (source : Generic.Occurrence (old runtime depth) (program runtime) (request runtime depth)
      (identityScope runtime) count) :
    actionEnvironment runtime depth count source =
      SourcePhysicalCalculation.rawEnvironment (runtime.advance (depth + (count + 1) + 1)) := by
  change Context.environment (statePoint process (scanIndex (R.mathCurrent (old runtime depth) (program runtime)
    (request runtime depth) (identityScope runtime) count).1.1 - 1)) = _
  have index := (congrArg scanIndex (source_original runtime depth count)).trans
    (actualScan (runtime.advance (depth + (count + 1) + 1)))
  exact (congrArg (fun value => Context.environment (PhysicalValue := SourceOperationInventoryLift.PairValue OperationValue)
    (statePoint process (value - 1))) index).trans (by rfl)

theorem source_action_environment
    (source : Generic.Occurrence (old runtime depth) (program runtime) (request runtime depth)
      (identityScope runtime) count) :
    (fun sort name => (Context.binding sort name).eval
      (SourcePhysicalCalculation.rawEnvironment (runtime.advance (depth + (count + 1))))) =
        actionEnvironment runtime depth count source :=
  (Context.binding_eval (PhysicalValue := SourceOperationInventoryLift.PairValue OperationValue)
    (runtime.advance (depth + (count + 1)))).trans
      (action_environment_actual runtime depth count source).symm

theorem physical_pair_actual
    (source : Generic.Occurrence (old runtime depth) (program runtime) (request runtime depth)
      (identityScope runtime) count) :
    ((physicalPayload runtime depth count source).sourceState,
      (physicalPayload runtime depth count source).forcedTrace) =
        ((payloadAt (runtime.advance (depth + (count + 1) + 1))).sourceState,
          (payloadAt (runtime.advance (depth + (count + 1) + 1))).forcedTrace) := by
  apply Prod.ext
  · exact (physicalPayload runtime depth count source).sourceState_eq.trans
      ((congrArg sourceStateAt (source_original runtime depth count)).trans
        (payloadAt (runtime.advance (depth + (count + 1) + 1))).sourceState_eq.symm)
  · exact (physicalPayload runtime depth count source).forcedTrace_eq.trans
      ((congrArg (fun current => (operationValuesAt current).sum) (source_original runtime depth count)).trans
        (payloadAt (runtime.advance (depth + (count + 1) + 1))).forcedTrace_eq.symm)

def registered := Generic.nextRegistered (old runtime depth) (program runtime) (request runtime depth)
  (identityScope runtime) count (actionEnvironment runtime depth count)

theorem registered_environment : (registered runtime depth count).input.environment =
    SourcePhysicalCalculation.rawEnvironment (runtime.advance (depth + (count + 1) + 1)) :=
  (Generic.environment_actual (old runtime depth) (program runtime) (request runtime depth)
    (identityScope runtime) count (actionEnvironment runtime depth count)).trans
      (action_environment_actual runtime depth count _)

def inquiry := Generic.inquiry (old runtime depth) (program runtime) (request runtime depth)
  (identityScope runtime) count (actionEnvironment runtime depth count)

theorem initial_kind : ((inquiry runtime depth count).tickAt 0).resolutionKind = .debtAdmission :=
  Generic.initial_kind (old runtime depth) (program runtime) (request runtime depth)
    (identityScope runtime) count (actionEnvironment runtime depth count)

theorem actual_node (nextDepth : Nat) :
    ((inquiry runtime depth count).stateAt (nextDepth + 1)).engine.node = .active
      (RootGeneratedDebtActivationJointSource.Native.Request.mathPresentation
        (currentState runtime depth count) (R.nextProgram (old runtime depth) (program runtime)
          (request runtime depth) (identityScope runtime))
        (registered runtime depth count)
        (R.nextScope (old runtime depth) (program runtime) (request runtime depth) (identityScope runtime)) nextDepth) :=
  Generic.actual_node (old runtime depth) (program runtime) (request runtime depth)
    (identityScope runtime) count (actionEnvironment runtime depth count) nextDepth

theorem completed_budget (zero : Consumer.budget runtime depth = 0)
    (paid : remaining (R.mathCurrent (old runtime depth) (program runtime) (request runtime depth)
      (identityScope runtime) count).2.state.1 = 0) :
    remaining (registered runtime depth count).input.expression = 14 := by
  have generated := Generic.budget (old runtime depth) (program runtime) (request runtime depth)
    (identityScope runtime) count (actionEnvironment runtime depth count)
  change remaining (registered runtime depth count).input.expression = _ at generated
  rw [ResidualSource.completed_budget runtime depth zero, paid] at generated
  exact generated

end
end SourcePhysicalCalculationAdmission.Inquiry.Continuation.Residual.Next
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
