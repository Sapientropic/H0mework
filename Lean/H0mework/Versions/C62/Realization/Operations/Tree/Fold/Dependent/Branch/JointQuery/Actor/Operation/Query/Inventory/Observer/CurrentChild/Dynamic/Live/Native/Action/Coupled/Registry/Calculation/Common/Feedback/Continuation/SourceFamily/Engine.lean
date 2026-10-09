import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Stage
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Admission
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace Lower.SourceFamily
variable {S : Type u} (W : S → Type u) [∀ t,AddCommGroup (W t)]
local instance familyEngineGroup (n : Nat) (t : S) : AddCommGroup (Lower.Value W n t) := Lower.groups W n t
variable {W} {X : S → Type u} {s : S}
namespace Admission
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockAdmission
 (presentation generatedAction query compiles target_root sourceRoot sourceEvent)
end Admission
namespace StockObservation
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockObservation
 (current current_observation read root)
end StockObservation
namespace Transport
variable {Y Z : S → Type u}
theorem current_eq (same : Y=Z) (f : Factory W Z s) (n : Nat) (data : Packet (W:=W) (X:=Y) (s:=s) n) :
 StockObservation.current data.1 (cfg (same.symm ▸ f) n data.2)=
 StockObservation.current (same ▸ data : Packet (W:=W) (X:=Z) (s:=s) n).1
  (cfg f n (same ▸ data : Packet (W:=W) (X:=Z) (s:=s) n).2) := by
 cases same; rfl

theorem root_heq (same : Y=Z) (f : Factory W Z s) (n : Nat) (data : Packet (W:=W) (X:=Y) (s:=s) n) :
 HEq (StockObservation.root data.1 (cfg (same.symm ▸ f) n data.2))
 (StockObservation.root (same ▸ data : Packet (W:=W) (X:=Z) (s:=s) n).1
  (cfg f n (same ▸ data : Packet (W:=W) (X:=Z) (s:=s) n).2)) := by
 cases same; rfl

end Transport
variable (factory : Factory W X s)
variable (initial : M.Frame (Value:=W) (Var:=X) (sort:=s))
variable (firstCfg : A.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
variable (language : firstCfg.LowVar=X)
def presentationAt (n : Nat) := Admission.presentation (frameAt factory initial firstCfg language n) (cfgAt factory initial firstCfg language n)
 (scalarAt factory initial firstCfg language n) (pairAt factory initial firstCfg language n) (nextCfg factory initial firstCfg language n)
def generated (n : Nat) := Admission.generatedAction (frameAt factory initial firstCfg language n) (cfgAt factory initial firstCfg language n)
 (scalarAt factory initial firstCfg language n) (pairAt factory initial firstCfg language n) (nextCfg factory initial firstCfg language n)
def queryAt (n : Nat) := Admission.query (frameAt factory initial firstCfg language n) (cfgAt factory initial firstCfg language n)

theorem presentation_current (n : Nat) : (presentationAt factory initial firstCfg language n).erase=
 StockObservation.current (frameAt factory initial firstCfg language n) (cfgAt factory initial firstCfg language n) := rfl

theorem target_current (n : Nat) :
 StockObservation.current (receiverAt factory initial firstCfg language n) (nextCfg factory initial firstCfg language n)=
 StockObservation.current (frameAt factory initial firstCfg language (n+1)) (cfgAt factory initial firstCfg language (n+1)) := by
 cases n with
 | zero => exact Transport.current_eq language factory 1 ⟨Lower.Stock.receiver initial firstCfg language,Lower.Stock.seed initial firstCfg language⟩
 | succ _ => rfl

theorem next_full_root (n : Nat) : HEq (StockObservation.root (frameAt factory initial firstCfg language (n+1)) (cfgAt factory initial firstCfg language (n+1)))
 (generated factory initial firstCfg language n).target.targetRoot := by
 have generatedRoot := Admission.target_root (frameAt factory initial firstCfg language n) (cfgAt factory initial firstCfg language n)
  (scalarAt factory initial firstCfg language n) (pairAt factory initial firstCfg language n) (nextCfg factory initial firstCfg language n)
  (Admission.sourceEvent (frameAt factory initial firstCfg language n) (cfgAt factory initial firstCfg language n))
 have actual : HEq (StockObservation.root (receiverAt factory initial firstCfg language n) (nextCfg factory initial firstCfg language n))
  (StockObservation.root (frameAt factory initial firstCfg language (n+1)) (cfgAt factory initial firstCfg language (n+1))) := by
  cases n with
  | zero => exact Transport.root_heq language factory 1 ⟨Lower.Stock.receiver initial firstCfg language,Lower.Stock.seed initial firstCfg language⟩
  | succ _ => rfl
 exact actual.symm.trans (heq_of_eq generatedRoot.symm)

theorem canonical_erasure (n : Nat) : (presentationAt factory initial firstCfg language (n+1)).erase=
 ⟨(generated factory initial firstCfg language n).target.TargetN,(generated factory initial firstCfg language n).target.targetAnswerAndNext.nextCurrent⟩ :=
 (presentation_current factory initial firstCfg language (n+1)).trans
 ((target_current factory initial firstCfg language n).symm.trans
  (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockAdmission.target_erasure
   (frameAt factory initial firstCfg language n) (cfgAt factory initial firstCfg language n)
   (scalarAt factory initial firstCfg language n) (pairAt factory initial firstCfg language n) (nextCfg factory initial firstCfg language n)))
theorem query_unique (n : Nat) (candidate : (presentationAt factory initial firstCfg language n).Query) : candidate=queryAt factory initial firstCfg language n :=
 SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Original.query_unique
 (frameAt factory initial firstCfg language n) (cfgAt factory initial firstCfg language n) candidate

theorem successor_valid (n : Nat) (candidate : (presentationAt factory initial firstCfg language n).Query) :
 (presentationAt factory initial firstCfg language (n+1)).erase=(RootInquiryProcessNode.answered (presentationAt factory initial firstCfg language n) candidate).erase ∧
 (.active (presentationAt factory initial firstCfg language n) : RootInquiryProcessNode).PreservesGeneratedLivingLawAt candidate (.active (presentationAt factory initial firstCfg language (n+1))) := by
 cases query_unique factory initial firstCfg language n candidate
 exact RootInquiryProcessNode.active_debtAdmission_successor_valid
  (presentationAt factory initial firstCfg language n) (presentationAt factory initial firstCfg language (n+1))
  (queryAt factory initial firstCfg language n) (generated factory initial firstCfg language n)
  (Admission.compiles (frameAt factory initial firstCfg language n) (cfgAt factory initial firstCfg language n)
   (scalarAt factory initial firstCfg language n) (pairAt factory initial firstCfg language n) (nextCfg factory initial firstCfg language n))
  (canonical_erasure factory initial firstCfg language n) (next_full_root factory initial firstCfg language n)

variable {T : Type u} {V Z : T → Type u} [∀ t,AddCommGroup (V t)] {t : T}
variable (other : M.Frame (Value:=V) (Var:=Z) (sort:=t))
variable (otherCfg : A.Programme (PhysicalValue:=V) (PhysicalVar:=Z) (sort:=t))
theorem stock_eq_of_current (n : Nat)
 (same : StockObservation.current (frameAt factory initial firstCfg language n) (cfgAt factory initial firstCfg language n)=StockObservation.current other otherCfg) :
 Lower.Stock.size (frameAt factory initial firstCfg language n)=Lower.Stock.size other := by
 have reads := congrArg RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.observation same
 rw [StockObservation.current_observation,StockObservation.current_observation] at reads
 have content := congrArg ULift.down (eq_of_heq (Sigma.mk.inj reads).2)
 exact congrArg Prod.snd content

theorem erasure_injective : Function.Injective (fun n => (presentationAt factory initial firstCfg language n).erase) := by
 intro first second same
 change (presentationAt factory initial firstCfg language first).erase=(presentationAt factory initial firstCfg language second).erase at same
 rw [presentation_current,presentation_current] at same
 exact (stock_strictMono factory initial firstCfg language).injective
  (stock_eq_of_current factory initial firstCfg language (frameAt factory initial firstCfg language second) (cfgAt factory initial firstCfg language second) first same)
end Lower.SourceFamily
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
