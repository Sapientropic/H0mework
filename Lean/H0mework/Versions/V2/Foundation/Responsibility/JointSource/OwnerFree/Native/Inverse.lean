import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Runtime
import H0mework.Versions.R2.Realization.Operations.NativeState
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.OwnerFree.Native
open SourceOperationEffects
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : SourceNativeAuthoritativeRootClosure N V) (origin : V.Current)
variable {Sorts : Type u} {Value Var : Sorts → Type u}
  [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (reader : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin →
  Raw (Value := Value) (Var := Var) (sort := sort))

theorem successor_injective : Function.Injective (process old origin reader).successor := by
  intro left right same
  have numbers := congrArg ULift.down same
  change left.down + 1 = right.down + 1 at numbers
  apply ULift.ext
  exact Nat.add_right_cancel numbers

/-- The existing pullback recovers the full native word on the actual source-action image. -/
def backward : SourceOperationNative.Carrier (process old origin reader) →ₗ[ℤ]
    SourceOperationNative.Carrier (process old origin reader) :=
  Finsupp.lcomapDomain (process old origin reader).successor (successor_injective old origin reader)

theorem backward_source (word : SourceOperationNative.Carrier (process old origin reader)) :
    backward old origin reader (SourceOperationNative.sourceAction (process old origin reader) word) = word :=
  Finsupp.leftInverse_lcomapDomain_mapDomain (process old origin reader).successor
    (successor_injective old origin reader) word

theorem previous_runtime (runtime : Runtime old origin reader) :
    backward old origin reader (SourceOperationNative.point runtime.tick.next) = SourceOperationNative.point runtime := by
  rw [← SourceOperationNative.sourceAction_point]
  exact backward_source old origin reader _

end RootGeneratedDebtActivationJointSource.OwnerFree.Native
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
