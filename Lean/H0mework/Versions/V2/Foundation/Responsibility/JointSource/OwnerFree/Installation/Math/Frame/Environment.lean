import H0mework.Versions.PR.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Frame.Source

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.Environment
open SourceOperationEffects
open RootGeneratedDebtActivationJointSource.OwnerFree
open RootGeneratedDebtActivationJointSource.OwnerFree.Installation
open RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (sourceRoot : SourceNativeLivingRootClosure N V)
variable (sourceVisit : SourceNativeTemporalVisitAt sourceRoot.toAuthoritativeRoot.toLedgerRoot)
variable (sourceU7 : U7ProducerCalculus N)
variable (sourceCalculus : U7ObstructionEvolutionCalculus N sourceU7)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (reader : sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt sourceVisit.current →
  Raw (Value:=Value) (Var:=Var) (sort:=sort))
private theorem material_environment
    (occurrence : (endpointState sourceRoot sourceVisit sourceU7 sourceCalculus reader).root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
      (endpointState sourceRoot sourceVisit sourceU7 sourceCalculus reader).visit.current) :
    (residualMaterial sourceRoot sourceVisit sourceU7 sourceCalculus reader occurrence).environment =
      (RootGeneratedDebtActivationJointSource.OwnerFree.raw (original sourceRoot) sourceVisit.current reader).environment := by
  rcases occurrence with ⟨support,event⟩
  cases event
  rfl
private theorem material_increment
    (occurrence : (endpointState sourceRoot sourceVisit sourceU7 sourceCalculus reader).root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
      (endpointState sourceRoot sourceVisit sourceU7 sourceCalculus reader).visit.current) :
    (residualMaterial sourceRoot sourceVisit sourceU7 sourceCalculus reader occurrence).increment = 0 := by
  rcases occurrence with ⟨support,event⟩
  cases event
  rfl

theorem raw_environment :
    (frame sourceRoot sourceVisit sourceU7 sourceCalculus reader).rawRead.environment =
      (RootGeneratedDebtActivationJointSource.OwnerFree.raw (original sourceRoot) sourceVisit.current reader).environment := by
  rw [RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.raw_environment]
  change (residualMaterial sourceRoot sourceVisit sourceU7 sourceCalculus reader _).environment +
    (residualMaterial sourceRoot sourceVisit sourceU7 sourceCalculus reader _).increment = _
  rw [material_environment, material_increment, add_zero]
end RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.Environment
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
