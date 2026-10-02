import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Request.Completion
import H0mework.Foundation.Responsibility.JointSource.Native.ResidualRequest

/-! A current's actual paid relation is read before its next request is emitted.
The environment reader is a source interface; concrete providers must fix its
actual action provenance. It does not certify an arbitrary environment update. -/

set_option autoImplicit false
universe u r

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Request.Residual

open SourceOperationEffects SourceOperationExecution RootInquiryCompletion
open SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual

noncomputable section
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : RootInquiryStateAt N V)
variable (program : Program old.root.toAuthoritativeRoot.toLedgerRoot)
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
  old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current)
variable (scope : IdentityScope program) (depth : Nat)

abbrev currentState := mathState old program registered scope depth
abbrev lower := (currentState old program registered scope depth).root.toAuthoritativeRoot.toLedgerRoot
abbrev current := (currentState old program registered scope depth).visit.current
abbrev Occurrence := (lower old program registered scope depth).source.source.toRootSource.actual.OccurrenceAt
  (current old program registered scope depth)

variable (environmentAt : Occurrence old program registered scope depth → Env Value Var)

def material (source : Occurrence old program registered scope depth) :
    Native.ResidualRequest.MaterialAt (Value := Value) (Var := Var) (sort := sort) source := by
  rcases source with ⟨support, event⟩
  cases event
  exact { environment := registered.input.environment
          increment := environmentAt ((lower old program registered scope depth).emitted
            (current old program registered scope depth)) - registered.input.environment
          raw := registered.input.expression
          state := (mathCurrent old program registered scope depth).2.state
          owner := mathEntry old program registered scope depth }

def reader (source : Occurrence old program registered scope depth) :=
  Native.ResidualRequest.input (material old program registered scope depth environmentAt source)

def nextRegistered := register (reader old program registered scope depth environmentAt)

def actualMaterial := material old program registered scope depth environmentAt
  ((lower old program registered scope depth).emitted (current old program registered scope depth))

theorem environment_actual : (nextRegistered old program registered scope depth environmentAt).input.environment =
    environmentAt ((lower old program registered scope depth).emitted (current old program registered scope depth)) := by
  change registered.input.environment +
    (environmentAt _ - registered.input.environment) = _
  abel

theorem owner_actual : (nextRegistered old program registered scope depth environmentAt).input.owner =
    (currentState old program registered scope depth).entryAt PUnit.unit := rfl

theorem history_actual : (actualMaterial old program registered scope depth environmentAt).state =
    (mathCurrent old program registered scope depth).2.state := rfl

theorem budget : remaining (nextRegistered old program registered scope depth environmentAt).input.expression =
    remaining registered.input.expression +
      remaining (mathCurrent old program registered scope depth).2.state.1 + 2 :=
  Native.ResidualRequest.budget (actualMaterial old program registered scope depth environmentAt)

variable {R : Type r} [CommRing R] [∀ sort, Module R (Value sort)]

theorem relation_actual : relationMap (R := R) registered.input.environment
    (Native.ResidualRequest.relations (R := R) (actualMaterial old program registered scope depth environmentAt)) =
      Finsupp.single registered.input.expression (1 : R) -
        Finsupp.single (mathCurrent old program registered scope depth).2.state.1 (1 : R) :=
  Native.ResidualRequest.relation_boundary (actualMaterial old program registered scope depth environmentAt)

theorem residual_actual :
    (residualEquivRange (evaluation (R := R) (nextRegistered old program registered scope depth environmentAt).input.environment)
      (canonicalResidual (evaluation (R := R) (nextRegistered old program registered scope depth environmentAt).input.environment)
        (relationMap (R := R) registered.input.environment
          (Native.ResidualRequest.relations (R := R) (actualMaterial old program registered scope depth environmentAt))))).val =
      (nextRegistered old program registered scope depth environmentAt).input.expression.eval
        (nextRegistered old program registered scope depth environmentAt).input.environment :=
  Native.ResidualRequest.residual_value (actualMaterial old program registered scope depth environmentAt)

end
end RootGeneratedDebtActivationJointSource.Native.Request.Residual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
