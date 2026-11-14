import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Future.Read
import H0mework.Realization.ObservationActions.Algebraic
set_option autoImplicit false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
namespace Future.History
namespace D
export SourceGeneratedActionObservationHistory.AlgebraicDependent
 (Prefix advance evaluator data compatible completion sourceMap readPrefix source_prefix source_fibre successor successor_source)
end D
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
local instance historyGroup (n : Nat) (t : S) : AddCommGroup (Lower.Value W n t) := Lower.groups W n t
variable (initial : M.Frame (Value:=W) (Var:=X) (sort:=s))
variable (firstCfg : A.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
variable (language : firstCfg.LowVar=X)

abbrev Word (n : Nat) := Read.Word (W:=W) (X:=X) (s:=s) n
abbrev Stage (n : Nat) := PairValue (PairValue (Lower.Value W (n+1))) s

def action (n : Nat) : Word (W:=W) (X:=X) (s:=s) n →ₗ[ℤ] Word (W:=W) (X:=X) (s:=s) (n+1) := liftMap

def observation (n : Nat) : Word (W:=W) (X:=X) (s:=s) n →ₗ[ℤ] Stage (W:=W) (s:=s) n :=
 updateInventory (R:=ℤ) (Read.beforeEnv initial firstCfg language n) (Read.increment initial firstCfg language n)

def data (n : Nat) := D.data (action (W:=W) (X:=X) (s:=s)) (observation initial firstCfg language) n

theorem compatible (n : Nat) : (data initial firstCfg language n).Compatible :=
 D.compatible (action (W:=W) (X:=X) (s:=s)) (observation initial firstCfg language) n

def completion (n : Nat) := (data initial firstCfg language n).Completion (compatible initial firstCfg language n)
def sourceMap (n : Nat) := D.sourceMap (action (W:=W) (X:=X) (s:=s)) (observation initial firstCfg language) n
def readPrefix (n bound : Nat) := D.readPrefix (action (W:=W) (X:=X) (s:=s)) (observation initial firstCfg language) n bound

theorem source_prefix (n bound : Nat) (word : Word (W:=W) (X:=X) (s:=s) n) : type_of%
 (D.source_prefix (action (W:=W) (X:=X) (s:=s)) (observation initial firstCfg language) n bound word) :=
 D.source_prefix _ _ _ _ _

theorem source_fibre (n : Nat) (left right : Word (W:=W) (X:=X) (s:=s) n) : type_of%
 (D.source_fibre (action (W:=W) (X:=X) (s:=s)) (observation initial firstCfg language) n left right) :=
 D.source_fibre _ _ _ _ _

def successor (n : Nat) := D.successor (action (W:=W) (X:=X) (s:=s)) (observation initial firstCfg language) n

theorem successor_source (n : Nat) (word : Word (W:=W) (X:=X) (s:=s) n) : type_of%
 (D.successor_source (action (W:=W) (X:=X) (s:=s)) (observation initial firstCfg language) n word) :=
 D.successor_source _ _ _ _
end Future.History
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
