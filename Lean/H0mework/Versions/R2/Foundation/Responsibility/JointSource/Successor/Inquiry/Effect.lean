import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Inquiry.Source
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Restructuring.Calculation

/-! The actual paid trace generates a residual relation. Its next source
calculation independently consumes the effect and the original inverse fibre. -/

set_option autoImplicit false
noncomputable section
universe u r
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Successor.Inquiry.Effect
open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarPresentation
open SourceGeneratedScalarDifferentialResidual RootInquiryCompletion CompilerFromPacketSourceLaw

variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable {R : Type r} [CommRing R] [∀ sort, Module R (Value sort)]
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : RootInquiryStateAt N V)
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
  old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current)
variable (packetAt : (current : V.Current) → Packet old.root.toAuthoritativeRoot.toLedgerRoot current)
variable (environment : {current : V.Current} →
  old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current → Env Value Var)
variable (depth : Nat)

def relations := Native.ResidualRequest.relations (R := R) (Source.actualMaterial old registered packetAt environment depth)

theorem relation_boundary : relationMap (R := R) (Source.rawRead old registered packetAt depth).environment
    (relations (R := R) old registered packetAt environment depth) =
      Finsupp.single (Source.rawRead old registered packetAt depth).expression (1 : R) -
        Finsupp.single (Source.paidRead old registered packetAt depth).state.1 (1 : R) :=
  Native.ResidualRequest.relation_boundary (R := R) (Source.actualMaterial old registered packetAt environment depth)

theorem request_effect :
    (Source.request old registered packetAt environment depth).input.expression.eval
      (Source.request old registered packetAt environment depth).input.environment =
    effectEvaluator (R := R) (Source.rawRead old registered packetAt depth).environment
      (Source.environmentAt old registered packetAt environment depth
        (Source.actualOccurrence old registered packetAt depth) - (Source.rawRead old registered packetAt depth).environment)
      (relationMap (R := R) (Source.rawRead old registered packetAt depth).environment
        (relations (R := R) old registered packetAt environment depth)) :=
  Native.ResidualRequest.updated_value (R := R) (Source.actualMaterial old registered packetAt environment depth)

theorem request_inverse_fibre :
    (residualEquivRange (evaluation (R := R) (Source.request old registered packetAt environment depth).input.environment)
      (canonicalResidual (evaluation (R := R) (Source.request old registered packetAt environment depth).input.environment)
        (relationMap (R := R) (Source.rawRead old registered packetAt depth).environment
          (relations (R := R) old registered packetAt environment depth)))).val =
      (Source.request old registered packetAt environment depth).input.expression.eval
        (Source.request old registered packetAt environment depth).input.environment :=
  Native.ResidualRequest.residual_value (R := R) (Source.actualMaterial old registered packetAt environment depth)

theorem relation_cochain : SourceOperationScalarCochain.boundary (R := R)
    (relationMap (R := R) (Source.rawRead old registered packetAt depth).environment
      (relations (R := R) old registered packetAt environment depth)) ∈
    LinearMap.range (relationMap (R := R)
      (mixedEnvironment (Source.rawRead old registered packetAt depth).environment
        (Source.environmentAt old registered packetAt environment depth
          (Source.actualOccurrence old registered packetAt depth) - (Source.rawRead old registered packetAt depth).environment))) :=
  (Source.actualMaterial old registered packetAt environment depth).state.2.relation_cochain (R := R)
    (Source.actualMaterial old registered packetAt environment depth).increment

def completedRequest := Restructuring.Calculation.completed
  (Source.currentState old registered packetAt depth).root.toAuthoritativeRoot
  (Source.request old registered packetAt environment depth) (Source.programme old registered packetAt depth)

theorem completed_request_effect : (completedRequest old registered packetAt environment depth).1 =
    effectEvaluator (R := R) (Source.rawRead old registered packetAt depth).environment
      (Source.environmentAt old registered packetAt environment depth
        (Source.actualOccurrence old registered packetAt depth) - (Source.rawRead old registered packetAt depth).environment)
      (relationMap (R := R) (Source.rawRead old registered packetAt depth).environment
        (relations (R := R) old registered packetAt environment depth)) :=
  (Restructuring.Calculation.completed_value
    (Source.currentState old registered packetAt depth).root.toAuthoritativeRoot
    (Source.request old registered packetAt environment depth) (Source.programme old registered packetAt depth)).trans
    (request_effect (R := R) old registered packetAt environment depth)

theorem completed_request_inverse_fibre :
    (residualEquivRange (evaluation (R := R) (Source.request old registered packetAt environment depth).input.environment)
      (canonicalResidual (evaluation (R := R) (Source.request old registered packetAt environment depth).input.environment)
        (relationMap (R := R) (Source.rawRead old registered packetAt depth).environment
          (relations (R := R) old registered packetAt environment depth)))).val =
      (completedRequest old registered packetAt environment depth).1 :=
  (request_inverse_fibre (R := R) old registered packetAt environment depth).trans
    (Restructuring.Calculation.completed_value
      (Source.currentState old registered packetAt depth).root.toAuthoritativeRoot
      (Source.request old registered packetAt environment depth) (Source.programme old registered packetAt depth)).symm

end RootGeneratedDebtActivationJointSource.Successor.Inquiry.Effect
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
