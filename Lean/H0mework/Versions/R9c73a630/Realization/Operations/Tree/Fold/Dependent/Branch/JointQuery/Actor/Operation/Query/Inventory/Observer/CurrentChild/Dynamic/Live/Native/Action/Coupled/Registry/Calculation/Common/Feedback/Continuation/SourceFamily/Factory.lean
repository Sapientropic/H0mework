import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace Lower.SourceFamily
variable {S : Type u} (W : S → Type u) [∀ t,AddCommGroup (W t)]
local instance familyFactoryGroup (n : Nat) (t : S) : AddCommGroup (Lower.Value W n t) := Lower.groups W n t
variable (X : S → Type u) (s : S)
abbrev Seed (n : Nat) := RootedAccountedUnfolding (PresentedRelationEventAt (Expr (Lower.Value W n) X s))
structure Factory where
 datum : (n : Nat) → Seed W X s n → (frame : M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s)) →
  SourceOperationInquiry.Context.Faces.Execution.Activation.SourceDatum (PhysicalValue:=Lower.Value W n) (PhysicalVar:=X) (sort:=s) X frame
 nextInventory : (n : Nat) → Seed W X s n → M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s) → Option (Seed W X s n)
 nextPairInventory : (n : Nat) → Seed W X s n → M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s) →
  Option (RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue (Lower.Value W n)) X s)))
 extraScalar : (n : Nat) → Seed W X s n → M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s) →
  Option (RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue (Lower.Value W n)) X s)))
 extraPair : (n : Nat) → Seed W X s n → M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s) →
  Option (RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue (PairValue (Lower.Value W n))) X s)))
variable {W X s}
variable (factory : Factory W X s)
def cfg (n : Nat) (seed : Seed W X s n) : A.Programme (PhysicalValue:=Lower.Value W n) (PhysicalVar:=X) (sort:=s) where
 LowVar:=X
 datum:=factory.datum n seed
 nextInventory:=factory.nextInventory n seed
 nextPairInventory:=factory.nextPairInventory n seed
abbrev Packet (n : Nat) := M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s) × Seed W X s n
variable (n : Nat) (data : Packet (W:=W) (X:=X) (s:=s) n)
def scalar := T.preserve (factory.extraScalar n data.2 data.1) (Lower.Stock.scalar data.1 (cfg factory n data.2) rfl)
def pair := T.preserve (factory.extraPair n data.2 data.1) (Lower.Stock.pair data.1 (cfg factory n data.2) rfl)
def receiver := B.initial data.1 (cfg factory n data.2) (scalar factory n data) (pair factory n data)
def nextSeed := SourceHistoryCommon.seed (scalar factory n data)
 (RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator (receiver factory n data).registered.input.expression))
def step : Packet (W:=W) (X:=X) (s:=s) (n+1) := ⟨receiver factory n data,nextSeed factory n data⟩

theorem seed_keeps_right {α : Type u} (first second : RootedAccountedUnfolding α) :
 second.trace.length≤(SourceHistoryCommon.seed first second).trace.length := by
 rw [SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock.seed_length]
 omega

theorem scalar_grows : Lower.Stock.size data.1<(scalar factory n data).trace.length := by
 have base := Lower.Stock.scalar_growth data.1 (cfg factory n data.2) rfl
 unfold scalar T.preserve
 cases factory.extraScalar n data.2 data.1 with
 | none => exact base
 | some prior =>
  have basele := seed_keeps_right prior (Lower.Stock.scalar data.1 (cfg factory n data.2) rfl)
  exact lt_of_lt_of_le base basele

variable (W X) (s)
def defaultFactory : Factory W X s where
 datum:=fun _ seed => (R.programme seed).datum
 nextInventory:=fun _ seed => (R.programme seed).nextInventory
 nextPairInventory:=fun _ seed => (R.programme seed).nextPairInventory
 extraScalar:=fun _ _ _ => none
 extraPair:=fun _ _ _ => none
variable {W X s}
theorem default_cfg (n : Nat) (seed : Seed W X s n) :
 cfg (defaultFactory W X s) n seed=R.programme seed := rfl

theorem default_transport {Y Z : S → Type u} (same : Y=Z) :
 (same.symm ▸ defaultFactory W Z s : Factory W Y s)=defaultFactory W Y s := by
 cases same; rfl

end Lower.SourceFamily
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
