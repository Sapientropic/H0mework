import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackSuccessorAction.Action
import H0mework.Versions.Rdf421ff6.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Future.Feedback.Binding
import H0mework.Versions.Rdf421ff6.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Future.Feedback.Action
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace Mother
namespace SF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily (Factory Seed Packet cfg scalar pair)
end SF
namespace M
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation (Frame)
end M
end Mother
namespace L
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower (Value groups)
end L
namespace SlotSource
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Future.Replay
 (physicalEnvironment physicalNext)
namespace Binding
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Future.Replay.Binding («at»)
end Binding
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (nextBorn actualOccurrence)
end Shared
end SlotSource

variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ target, AddCommGroup (Value target)] {sort : Sorts}
local instance sourceGroups (grade : Nat) (target : Sorts) : AddCommGroup
 (L.Value Value grade target) := L.groups Value grade target
variable (binding : ∀ target, Var target → Expr Value Var target)
variable (factory : Mother.SF.Factory Value Var sort)

/-- The decoder executes the actual source substitution at the same supplied originalOccurrence. Existing reader, component and all four inventories remain inherited. -/
def installedSourceFactory : Mother.SF.Factory Value Var sort :=
 { factory with datum := fun grade sourceSeed currentFrame =>
   { factory.datum grade sourceSeed currentFrame with
    nextEnvironmentReadAt := some (fun {_current} supplied _queryPaid =>
      SlotSource.physicalNext (SlotSource.Binding.at binding grade) currentFrame supplied) } }

variable (grade : Nat) (sourceSeed : Mother.SF.Seed Value Var sort grade)
variable (frame : Mother.M.Frame (Value:=L.Value Value grade) (Var:=Var) (sort:=sort))

theorem source_decoder_actual_occurrence
 {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current)) (queryPaid) :
 (((installedSourceFactory binding factory).datum grade sourceSeed frame).nextEnvironmentReadAt.get (by rfl)) supplied queryPaid=
 SourceOperationScalarPresentation.SourceSubstitution.sourceEnvironment (SlotSource.Binding.at binding grade)
  (SlotSource.physicalEnvironment frame supplied) := rfl

theorem source_factory_preserves_complete_callbacks :
 (installedSourceFactory binding factory).nextInventory=factory.nextInventory ∧
 (installedSourceFactory binding factory).nextPairInventory=factory.nextPairInventory ∧
 (installedSourceFactory binding factory).extraScalar=factory.extraScalar ∧
 (installedSourceFactory binding factory).extraPair=factory.extraPair := ⟨rfl,rfl,rfl,rfl⟩

/-- Generated source action, not an after-vector equality premise, enters the real born environment. -/
theorem source_decoder_born_environment
 (bornCurrent)
 (occurrence : (SlotSource.Shared.nextBorn frame (Mother.SF.cfg (installedSourceFactory binding factory) grade sourceSeed)).old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt bornCurrent) :
 (SlotSource.Shared.nextBorn frame (Mother.SF.cfg (installedSourceFactory binding factory) grade sourceSeed)).environment occurrence=
 SlotSource.physicalNext (SlotSource.Binding.at binding grade) frame (SlotSource.Shared.actualOccurrence frame) := rfl
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
