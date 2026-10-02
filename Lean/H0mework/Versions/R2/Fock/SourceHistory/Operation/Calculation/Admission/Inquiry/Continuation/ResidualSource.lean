import H0mework.Versions.R2.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Continuation.Source
import H0mework.Foundation.Responsibility.JointSource.Native.ResidualRequest

/-! The actual old paid history supplies the residual request; its environment
is updated to the physical actor at that same source occurrence. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePhysicalCalculationAdmission.Inquiry.Continuation.ResidualSource

open SourceOperationEffects SourceOperationNative SourceOperationExecution SourceOperationScalarRelations
open SourceGeneratedScalarDifferentialResidual
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationPrefix

noncomputable section
variable (runtime : LivingRuntimeState process) (depth : Nat)

def material
    (source : (lower runtime).source.source.toRootSource.actual.OccurrenceAt (current runtime depth)) :
    RootGeneratedDebtActivationJointSource.Native.ResidualRequest.MaterialAt
      (Value := SourcePhysicalCalculation.CalculationValue) (Var := SourcePhysicalCalculation.CalculationVar)
      (sort := Sum.inl OperationSort.parent) source := by
  rcases source with ⟨support, event⟩
  cases event
  exact { environment := SourcePhysicalCalculation.rawEnvironment runtime
          increment := rawEnvironment runtime depth - SourcePhysicalCalculation.rawEnvironment runtime
          raw := SourcePhysicalCalculation.rawExpression
          state := oldHistory runtime depth
          owner := mathEntry runtime depth }

def reader
    (source : (lower runtime).source.source.toRootSource.actual.OccurrenceAt (current runtime depth)) :=
  RootGeneratedDebtActivationJointSource.Native.ResidualRequest.input (material runtime depth source)

def registered := RootGeneratedDebtActivationJointSource.register (reader runtime depth)

def sourceMaterial := material runtime depth (occurrence runtime depth)

theorem environment_actual : (registered runtime depth).input.environment = rawEnvironment runtime depth := by
  change SourcePhysicalCalculation.rawEnvironment runtime +
    (rawEnvironment runtime depth - SourcePhysicalCalculation.rawEnvironment runtime) = _
  abel

theorem owner_actual : (registered runtime depth).input.owner = mathEntry runtime depth := rfl

theorem state_actual : (sourceMaterial runtime depth).state = oldHistory runtime depth := rfl

theorem expression_actual : (registered runtime depth).input.expression =
    RootGeneratedDebtActivationJointSource.Native.ResidualRequest.expression (sourceMaterial runtime depth) := rfl

theorem value_actual : (registered runtime depth).input.expression.eval (registered runtime depth).input.environment =
    Consumer.physicalPair runtime depth -
      (Consumer.history runtime depth).1.eval (Consumer.physicalEnvironment runtime depth) := by
  rw [expression_actual, environment_actual]
  apply (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.expression_eval
    (sourceMaterial runtime depth) (rawEnvironment runtime depth)).trans
  change SourcePhysicalCalculation.rawExpression.eval (rawEnvironment runtime depth) -
    (oldHistory runtime depth).1.eval (rawEnvironment runtime depth) = _
  rw [rawEnvironment_actual, oldHistory_actual, Consumer.current_pair_read]

theorem residual_actual :
    (residualEquivRange (evaluation (R := ℤ) (Consumer.physicalEnvironment runtime depth))
      (canonicalResidual (evaluation (R := ℤ) (Consumer.physicalEnvironment runtime depth))
        (Consumer.boundary runtime depth))).val =
      (registered runtime depth).input.expression.eval (registered runtime depth).input.environment :=
  (Consumer.residual_read runtime depth).trans (value_actual runtime depth).symm

theorem completed_value (zero : Consumer.budget runtime depth = 0) :
    (registered runtime depth).input.expression.eval (registered runtime depth).input.environment =
      Consumer.physicalPair runtime depth -
        ((payloadAt runtime).sourceState, (payloadAt runtime).forcedTrace) :=
  (residual_actual runtime depth).symm.trans (Consumer.zero_budget_residual runtime depth zero)

theorem completed_budget (zero : Consumer.budget runtime depth = 0) :
    remaining (registered runtime depth).input.expression = 12 := by
  have actual : remaining (registered runtime depth).input.expression =
      10 + Consumer.budget runtime depth + 2 :=
    RootGeneratedDebtActivationJointSource.Native.ResidualRequest.budget (sourceMaterial runtime depth)
  rw [zero] at actual
  exact actual

end
end SourcePhysicalCalculationAdmission.Inquiry.Continuation.ResidualSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
