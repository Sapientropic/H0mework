import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Effect.Words
import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Future.Feedback.Installation
import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Installed
import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Future.First
import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Future.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual RootLawDependentJointStateController CofinalHistorySettlement


namespace Lower.SourceFamily.Effect.PaidSource
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
local instance familyGroups (n : Nat) (t : S) : AddCommGroup (Lower.Value W n t) := Lower.groups W n t

def Paid (f : M.Frame (Value:=W) (Var:=X) (sort:=s)) : Prop :=
 ∃ paid : DebtActivationWorld.GeneratedStepAt
 (RootGeneratedDebtActivationJointSource.Idle.law f.registered.input.environment f.registered.input.expression)
 f.event.state, f.action=.inr paid

theorem paid_of_budget (f : M.Frame (Value:=W) (Var:=X) (sort:=s))
 (positive : 0<remaining f.event.state.1) : Paid f := by
 unfold Paid
 cases selected : f.action with
 | inr paid => exact ⟨paid,rfl⟩
 | inl settled =>
  have zero := (SourceOperationExecutionDebt.law f.registered.input.environment f.registered.input.expression).settlement_budget_zero settled
  change remaining f.event.state.1=0 at zero
  omega

theorem cast_paid {Y Z : S → Type u} (same : Y=Z) (n : Nat)
 (data : Lower.SourceFamily.Packet (W:=W) (X:=Y) (s:=s) n) (paid : Paid data.1) :
 Paid (same ▸ data : Lower.SourceFamily.Packet (W:=W) (X:=Z) (s:=s) n).1 := by
 cases same; exact paid

private theorem receiver_positive
 (frame : M.Frame (Value:=W) (Var:=X) (sort:=s))
 (cfg : A.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
 (scalar : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue W) cfg.LowVar s)))
 (pair : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue (PairValue W)) cfg.LowVar s))) :
 0<remaining (Future.receiver frame cfg scalar pair).event.state.1 := by
 have fee := RootGeneratedDebtActivationJointSource.Native.ResidualRequest.budget (Future.Receipt.actualMaterial frame cfg)
 have consumed :
  remaining (RootGeneratedDebtActivationJointSource.initialEvent (Future.Receipt.registered frame cfg)).state.1=
  remaining (Future.Receipt.firstStep frame cfg).1.1+1 := by
  rcases Future.Receipt.firstStep frame cfg with ⟨target,step⟩
  cases step with
  | paid actual => exact actual.remaining_eq
 change remaining (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.expression (Future.Receipt.actualMaterial frame cfg))=
  remaining (Future.Receipt.actualMaterial frame cfg).raw+remaining (Future.Receipt.actualMaterial frame cfg).state.1+2 at fee
 rw [Future.receiver_state]
 have sourceFee :
  remaining (RootGeneratedDebtActivationJointSource.initialEvent (Future.Receipt.registered frame cfg)).state.1=
  remaining (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.expression (Future.Receipt.actualMaterial frame cfg)) := rfl
 omega

variable (originalBinding : ∀ t,X t → Expr W X t)
variable (initial : M.Frame (Value:=W) (Var:=X) (sort:=s))
variable (firstCfg : A.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
variable (language : firstCfg.LowVar=X)
theorem native_paid_from_raw (sourceFactory : Lower.SourceFamily.Factory W X s)
 (sourceCharge : ∀ n seed frame, 2≤remaining
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame
   (Lower.SourceFamily.cfg sourceFactory n seed)).raw.expression)
 (firstCharge : 2≤remaining (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query initial firstCfg).raw.expression)
 (n : Nat) : Paid (Lower.SourceFamily.frameAt sourceFactory initial firstCfg language (n+1)) := by
 cases n with
 | zero =>
  have positive := receiver_positive initial firstCfg (Lower.Stock.scalar initial firstCfg language)
   (Lower.Stock.pair initial firstCfg language)
  exact cast_paid language 1
   ⟨Lower.Stock.receiver initial firstCfg language,Lower.Stock.seed initial firstCfg language⟩
   (paid_of_budget (Lower.Stock.receiver initial firstCfg language) positive)
 | succ n =>
  let data := Lower.SourceFamily.tailData sourceFactory initial firstCfg language n
  have positive := receiver_positive data.1 (Lower.SourceFamily.cfg sourceFactory (n+1) data.2)
   (Lower.SourceFamily.scalar sourceFactory (n+1) data)
   (Lower.SourceFamily.pair sourceFactory (n+1) data)
  exact paid_of_budget (Lower.SourceFamily.receiver sourceFactory (n+1) data) positive

theorem native_paid (firstCharge : 2≤remaining (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query initial firstCfg).raw.expression)
 (n : Nat) : Paid (Lower.SourceFamily.frameAt (Lower.SourceFamily.Replay.factory (s:=s) originalBinding) initial firstCfg language (n+1)) := by
 cases n with
 | zero =>
  have positive := receiver_positive initial firstCfg (Lower.Stock.scalar initial firstCfg language)
   (Lower.Stock.pair initial firstCfg language)
  have paid := paid_of_budget (Lower.Stock.receiver initial firstCfg language) positive
  exact cast_paid language 1 ⟨Lower.Stock.receiver initial firstCfg language,Lower.Stock.seed initial firstCfg language⟩ paid
 | succ n =>
  let data := Lower.SourceFamily.tailData (Lower.SourceFamily.Replay.factory (s:=s) originalBinding) initial firstCfg language n
  exact Lower.SourceFamily.Effect.receiver_paid (Future.Replay.Binding.at originalBinding (n+1)) data.2 data.1
   (Lower.SourceFamily.scalar (Lower.SourceFamily.Replay.factory (s:=s) originalBinding) (n+1) data)
   (Lower.SourceFamily.pair (Lower.SourceFamily.Replay.factory (s:=s) originalBinding) (n+1) data)


theorem enhanced_native_paid (firstCharge : 2≤remaining (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query initial firstCfg).raw.expression)
 (n : Nat) : Paid (Lower.SourceFamily.frameAt (Lower.SourceFamily.Foresight.factory (s:=s) originalBinding) initial firstCfg language (n+1)) :=
 native_paid_from_raw initial firstCfg language (Lower.SourceFamily.Foresight.factory (s:=s) originalBinding)
  (Lower.SourceFamily.Foresight.factory_fee originalBinding) firstCharge n

end Lower.SourceFamily.Effect.PaidSource

namespace Lower.SourceFamily.Effect.Installed
namespace Activated
export Lower.SourceFamily.Replay.Activated (sourceFactory dataAt frameAt seedAt bindingAt runtime)
end Activated
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec : RecognitionAt H root)
local instance sourceGroups : ∀ t,AddCommGroup (Act.PhysicalValue root visit rec t) := inferInstance
local instance sourceFamilyGroups (n : Nat) (t : SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Slot root rec) :
 AddCommGroup (Lower.Value (Act.LowValue root visit rec) n t) := Lower.groups (Act.LowValue root visit rec) n t
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor sourceStage stage count : Nat)
theorem actual_native_paid (n : Nat) : Lower.SourceFamily.Effect.PaidSource.Paid (Activated.frameAt root visit rec U7 calculus anchor sourceStage stage count n) :=
 Lower.SourceFamily.Effect.PaidSource.native_paid_from_raw
  (initial root visit rec U7 calculus anchor sourceStage stage count)
  (firstCfg root visit rec U7 calculus anchor sourceStage stage)
  (language root visit rec U7 calculus anchor sourceStage stage)
  (Activated.sourceFactory root visit rec)
  (Foresight.Contextual.factory_fee
   (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.lowBinding root visit rec))
  (Future.First.actual_first_fee root visit rec U7 calculus anchor sourceStage stage count) n

end Lower.SourceFamily.Effect.Installed
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
