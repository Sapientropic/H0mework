import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Request.Source

set_option autoImplicit false
universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Request

open SourceOperationEffects RootInquiryCompletion

noncomputable section

private theorem project_congr (first second : AnyAuthoritativeRootCurrent.{u})
    (firstProjection : first.current.root.source.projectionLaw.Projection)
    (secondProjection : second.current.root.source.projectionLaw.Projection)
    (firstActive : first.current.root.source.projectionLaw.ActiveAt firstProjection
      (first.current.root.emitted first.current.visit.current))
    (secondActive : second.current.root.source.projectionLaw.ActiveAt secondProjection
      (second.current.root.emitted second.current.visit.current))
    (same : first = second) (projections : HEq firstProjection secondProjection)
    (active : HEq firstActive secondActive) :
    HEq (first.current.root.source.projectionLaw.project firstProjection
      (first.current.root.emitted first.current.visit.current) firstActive)
      (second.current.root.source.projectionLaw.project secondProjection
        (second.current.root.emitted second.current.visit.current) secondActive) := by
  cases same
  cases projections
  cases active
  rfl

variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : RootInquiryStateAt N V)
variable (program : Program old.root.toAuthoritativeRoot.toLedgerRoot)
variable (scope : IdentityScope program)

def eraseVisit (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
    old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current)
    (visit : SourceNativeTemporalVisitAt (targetRoot old program registered scope).toAuthoritativeRoot.toLedgerRoot) :
    AnyAuthoritativeRootCurrent.{u} :=
  ⟨NewN old registered, ⟨NewV old program registered, (targetRoot old program registered scope).toAuthoritativeRoot, visit⟩⟩

theorem input_eq_of_erasure
    (first second : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
      old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current)
    (firstVisit : SourceNativeTemporalVisitAt (targetRoot old program first scope).toAuthoritativeRoot.toLedgerRoot)
    (secondVisit : SourceNativeTemporalVisitAt (targetRoot old program second scope).toAuthoritativeRoot.toLedgerRoot)
    (same : eraseVisit old program scope first firstVisit = eraseVisit old program scope second secondVisit) :
    first.input = second.input := by
  exact eq_of_heq (project_congr (eraseVisit old program scope first firstVisit)
    (eraseVisit old program scope second secondVisit)
    ((registrationInstallation old program first scope).embed PUnit.unit)
    ((registrationInstallation old program second scope).embed PUnit.unit)
    PUnit.unit PUnit.unit same HEq.rfl HEq.rfl)

theorem registered_eq_of_erasure
    (first second : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
      old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current)
    (firstVisit : SourceNativeTemporalVisitAt (targetRoot old program first scope).toAuthoritativeRoot.toLedgerRoot)
    (secondVisit : SourceNativeTemporalVisitAt (targetRoot old program second scope).toAuthoritativeRoot.toLedgerRoot)
    (same : eraseVisit old program scope first firstVisit = eraseVisit old program scope second secondVisit) :
    first = second := by
  have inputs := input_eq_of_erasure old program scope first second firstVisit secondVisit same
  cases first
  cases second
  cases inputs
  rfl

end
end RootGeneratedDebtActivationJointSource.Native.Request
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
