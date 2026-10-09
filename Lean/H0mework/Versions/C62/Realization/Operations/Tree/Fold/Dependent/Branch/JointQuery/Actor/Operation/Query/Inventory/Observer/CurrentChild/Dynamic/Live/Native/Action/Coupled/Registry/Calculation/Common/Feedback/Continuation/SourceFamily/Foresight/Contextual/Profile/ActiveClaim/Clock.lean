import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.Source
import H0mework.Versions.PR.Foundation.Responsibility.JointSource.Successor.Inquiry.Continuation.Clock

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceOperationEffects SourceOperationExecution RootInquiryCompletion

namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
namespace Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.Clock
namespace Claim
export Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim (cfg source_charge)
end Claim
namespace Wr
export Lower.SourceFamily.Foresight.Contextual.Written (receiver)
end Wr
namespace Sealed
export SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceRegisteredClaimClock
  (currentRuntime sourceRemainder sourceBudget suffixHistory remainder_generated suffix_ends_at_original current_event)
end Sealed
variable {S : Type u} {W X : S → Type u} [∀t,AddCommGroup (W t)] {s : S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding : ∀t,X t→Expr W X t) (n : Nat)
variable (packet : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)

theorem active_remainder_positive : 0 < Sealed.sourceRemainder (Wr.receiver binding n packet) := by
  have charged := Future.receiver_budget packet.1 (Claim.cfg binding n packet)
    (Lower.SourceFamily.scalar (Lower.SourceFamily.Foresight.Contextual.factory (s:=s) binding) n packet)
    (Lower.SourceFamily.pair (Lower.SourceFamily.Foresight.Contextual.factory (s:=s) binding) n packet)
    (Claim.source_charge binding n packet)
  change 3 ≤ Sealed.sourceRemainder (Wr.receiver binding n packet) at charged
  omega

theorem active_suffix_completed : type_of% (Sealed.suffix_ends_at_original (Wr.receiver binding n packet)
    (active_remainder_positive binding n packet)) :=
  Sealed.suffix_ends_at_original (Wr.receiver binding n packet) (active_remainder_positive binding n packet)

theorem active_clock : 1+Sealed.sourceRemainder (Wr.receiver binding n packet) =
    Sealed.sourceBudget (Wr.receiver binding n packet) := by
  have budget := Sealed.remainder_generated (Wr.receiver binding n packet)
  have positive := active_remainder_positive binding n packet
  change Sealed.sourceRemainder (Wr.receiver binding n packet) = Sealed.sourceBudget (Wr.receiver binding n packet)-1 at budget
  omega

theorem active_current_event : type_of% (Sealed.current_event (Wr.receiver binding n packet)) :=
  Sealed.current_event (Wr.receiver binding n packet)

end Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.Clock
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
