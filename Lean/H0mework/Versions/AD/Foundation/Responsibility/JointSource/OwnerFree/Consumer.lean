import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Calculation
import H0mework.Realization.Operations.Execution.Relations

/-! The source-controlled normal target supplies its full trace and value.
That actual trace generates the relation and the original update inverse fibre. -/

set_option autoImplicit false
noncomputable section
universe u r
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.OwnerFree.Consumer
open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarPresentation
open SourceGeneratedScalarDifferentialResidual
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : SourceNativeAuthoritativeRootClosure N V) (origin : V.Current)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (reader : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin →
  Raw (Value := Value) (Var := Var) (sort := sort))
variable {R : Type r} [CommRing R] [∀ sort, Module R (Value sort)]

def targetState := runtimeCurrent old origin reader (Calculation.targetRuntime old origin reader)
def trace := (targetState old origin reader).2
def value := (Calculation.completed old origin reader).1

def originalMaterial : OriginalMaterial old origin :=
  (originalFace old origin reader (Calculation.targetRuntime old origin reader)).rootRead

def originalObservation : (old.source.observationAt (old.emitted origin)).1 :=
  (observationFace old origin reader (Calculation.targetRuntime old origin reader)).rootRead

theorem original_material : originalMaterial old origin reader =
    ⟨old.emitted origin, old.generatedLedgerAt origin, old.generatedPatchAt origin,
      old.source.restructuringSource.compiler.certifyRestructuring (old.emitted origin)⟩ := rfl

theorem original_observation : originalObservation old origin reader =
    (old.source.observationAt (old.emitted origin)).2 := rfl

theorem value_source : value old origin reader = (raw old origin reader).expression.eval
    (raw old origin reader).environment := Calculation.completed_value old origin reader

theorem target_expression : (targetState old origin reader).1 = .const (value old origin reader) :=
  (Calculation.completed old origin reader).2.down

theorem paid_history : (trace old origin reader).length = remaining (raw old origin reader).expression :=
  Calculation.completed_history old origin reader

def relations := (trace old origin reader).relationWords (R := R)

theorem relation_boundary : relationMap (R := R) (raw old origin reader).environment
    (relations (R := R) old origin reader) = Finsupp.single (raw old origin reader).expression (1 : R) -
      Finsupp.single (.const (value old origin reader)) (1 : R) := by
  have source := (trace old origin reader).relation_boundary (R := R)
  conv_rhs at source => rw [target_expression]
  exact source

theorem relation_old : evaluation (R := R) (raw old origin reader).environment
    (relationMap (R := R) (raw old origin reader).environment (relations (R := R) old origin reader)) = 0 :=
  (trace old origin reader).relation_old (R := R)

theorem updated_inverse_fibre (increment : Env Value Var) :
    (residualEquivRange (evaluation (R := R) ((raw old origin reader).environment + increment))
      (canonicalResidual (evaluation (R := R) ((raw old origin reader).environment + increment))
        (relationMap (R := R) (raw old origin reader).environment (relations (R := R) old origin reader)))).val =
      effectEvaluator (R := R) (raw old origin reader).environment increment
        (relationMap (R := R) (raw old origin reader).environment (relations (R := R) old origin reader)) :=
  (trace old origin reader).updated_residual (R := R) increment

theorem relation_cochain (increment : Env Value Var) : SourceOperationScalarCochain.boundary (R := R)
    (relationMap (R := R) (raw old origin reader).environment (relations (R := R) old origin reader)) ∈
      LinearMap.range (relationMap (R := R) (mixedEnvironment (raw old origin reader).environment increment)) :=
  (trace old origin reader).relation_cochain (R := R) increment

end RootGeneratedDebtActivationJointSource.OwnerFree.Consumer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
