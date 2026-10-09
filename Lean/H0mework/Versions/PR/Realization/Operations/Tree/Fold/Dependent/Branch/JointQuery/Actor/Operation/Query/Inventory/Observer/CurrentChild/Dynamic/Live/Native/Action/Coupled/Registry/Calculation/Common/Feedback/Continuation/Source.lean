import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Raw
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Faces.Laws
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace M
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation (Frame)
end M
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme)
end A
namespace C
export SourceGeneratedInquiryReceiptAction.Configured
 (lowInitial lowWritten lowPairWritten lowSeed lowProgramme)
end C
namespace R
variable {S : Type u} {W X : S → Type u} [∀ s,AddCommGroup (W s)] {s : S}
abbrev nativeProgramme := SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted.programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s)
def programme (seed : RootedAccountedUnfolding (CofinalHistorySettlement.PresentedRelationEventAt (Expr W X s))) :=
 SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Faces.Lower.configuration (nativeProgramme seed)
end R
namespace B
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Bootstrap
 (initial sourceRoot sourceEvent generatedAction presentation query target_root target_current target_erasure successor_valid)
end B
namespace Base
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry
 (observedRoot presentation)
end Base
namespace T
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock
 (preserve physicalPrior pairPrior liftEvent preserves_length mapped_length mapped_trace)
end T
namespace Lower
variable {S : Type u} (W : S → Type u) [∀ s,AddCommGroup (W s)]
def Value (n : Nat) : S → Type u := Nat.rec W (fun _ previous => PairValue previous) n
@[instance_reducible] def groups (n : Nat) : ∀ s,AddCommGroup (Value W n s) :=
 Nat.rec (fun s => (show AddCommGroup (W s) from inferInstance))
  (fun _ previous s => @Prod.instAddCommGroup _ _ (previous s) (previous s)) n
local instance stageGroup (n : Nat) (s : S) : AddCommGroup (Value W n s) := groups W n s
namespace Stock
variable {W} {X : S → Type u} {s : S}
variable (frame : M.Frame (Value:=W) (Var:=X) (sort:=s))
variable (cfg : A.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
variable (sameVar : cfg.LowVar=X)
def scalar : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue W) cfg.LowVar s)) :=
  T.preserve (sameVar.symm ▸ T.physicalPrior frame) (C.lowWritten frame cfg)
def pair : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue (PairValue W)) cfg.LowVar s)) :=
  T.preserve (sameVar.symm ▸ T.pairPrior frame) (C.lowPairWritten frame cfg)
def receiver := B.initial frame cfg (scalar frame cfg sameVar) (pair frame cfg sameVar)
def seed := SourceHistoryCommon.seed (scalar frame cfg sameVar)
  (RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator (receiver frame cfg sameVar).registered.input.expression))
def programme := R.programme (seed frame cfg sameVar)
theorem language : (programme frame cfg sameVar).LowVar=cfg.LowVar := rfl
theorem cast_length {Y Z : S → Type u} (same : Y=Z)
 (tree : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue W) Y s))) :
 (same ▸ tree).trace.length=tree.trace.length := by cases same; rfl

theorem cast_some {Y Z : S → Type u} (same : Y=Z)
 (tree : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue W) Y s))) :
 (same ▸ (some tree : Option (RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue W) Y s)))))=
 some (same ▸ tree) := by cases same; rfl

theorem trace_nonempty {α : Type u} (stock : RootedAccountedUnfolding α) : 0<stock.trace.length := by
 cases stock with
 | occur origin children => change 0<(origin::RootedAccountedUnfolding.traceBranches children).length; simp only [List.length_cons]; omega

def size (frame : M.Frame (Value:=W) (Var:=X) (sort:=s)) : Nat :=
 frame.inventory.elim 0 (fun stock => stock.trace.length)

theorem scalar_growth : size frame<(scalar frame cfg sameVar).trace.length := by
 unfold scalar
 generalize priorEq : frame.inventory=prior
 cases prior with
 | none =>
  have exactPrior : T.physicalPrior frame=none := by
   unfold T.physicalPrior; rw [priorEq]; rfl
  simp only [exactPrior]
  have base : size frame=0 := by unfold size; rw [priorEq]; rfl
  rw [base]
  exact trace_nonempty _
 | some stock =>
  have exactPrior : T.physicalPrior frame=some (stock.map (T.liftEvent (W:=W) (X:=X) (s:=s))) := by
   unfold T.physicalPrior; rw [priorEq]; rfl
  have base : size frame=stock.trace.length := by unfold size; rw [priorEq]; rfl
  rw [base]
  have grows := T.preserves_length
    (sameVar.symm ▸ stock.map (T.liftEvent (W:=W) (X:=X) (s:=s))) (C.lowWritten frame cfg)
  have traceSize : (sameVar.symm ▸ stock.map (T.liftEvent (W:=W) (X:=X) (s:=s))).trace.length=stock.trace.length :=
   (cast_length sameVar.symm _).trans (T.mapped_length _ _)
  rw [traceSize] at grows
  simpa only [exactPrior,cast_some] using grows

theorem cast_mem {Y Z : S → Type u} (same : Y=Z)
 (tree : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue W) Y s)))
 (event : PresentedRelationEventAt (Expr (PairValue W) Y s)) :
 (same ▸ event) ∈ (same ▸ tree).trace ↔ event ∈ tree.trace := by cases same; rfl

theorem carried_scalar (prior : RootedAccountedUnfolding (PresentedRelationEventAt (Expr W X s)))
 (present : frame.inventory=some prior) (event : PresentedRelationEventAt (Expr W X s)) (belongs : event ∈ prior.trace) :
 (sameVar.symm ▸ (T.liftEvent (W:=W) (X:=X) (s:=s) event)) ∈ (scalar frame cfg sameVar).trace := by
 have mapped : T.liftEvent (W:=W) (X:=X) (s:=s) event ∈
  (prior.map (T.liftEvent (W:=W) (X:=X) (s:=s))).trace := by
  rw [T.mapped_trace]
  exact List.mem_map_of_mem belongs
 have carried := (cast_mem sameVar.symm _ _).mpr mapped
 unfold scalar T.physicalPrior
 rw [present]
 change (sameVar.symm ▸ T.liftEvent event) ∈
  (T.preserve (sameVar.symm ▸ some (prior.map T.liftEvent)) (C.lowWritten frame cfg)).trace
 rw [cast_some]
 exact (SourceHistoryCommon.parallel_left _ _ _).1 _ carried

theorem receiver_size : size (receiver frame cfg sameVar)=(scalar frame cfg sameVar).trace.length := rfl
end Stock
end Lower
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
