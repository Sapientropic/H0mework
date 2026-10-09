import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Factory
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace Lower.SourceFamily
variable {S : Type u} (W : S → Type u) [∀ t,AddCommGroup (W t)]
local instance familyStageGroup (n : Nat) (t : S) : AddCommGroup (Lower.Value W n t) := Lower.groups W n t
variable {W} {X : S → Type u} {s : S}
namespace Transport
variable {Y Z : S → Type u}
theorem size_eq (same : Y=Z) (n : Nat) (data : Packet (W:=W) (X:=Y) (s:=s) n) :
 Lower.Stock.size data.1=Lower.Stock.size (same ▸ data : Packet (W:=W) (X:=Z) (s:=s) n).1 := by
 cases same; rfl
theorem frame_heq {Y Z : S → Type u} (same : Y=Z) (n : Nat) (data : Packet (W:=W) (X:=Y) (s:=s) n) :
 HEq data.1 (same ▸ data : Packet (W:=W) (X:=Z) (s:=s) n).1 := by
 cases same; rfl

theorem programme_heq {Y Z : S → Type u} (same : Y=Z) (f : Factory W Z s) (n : Nat) (data : Packet (W:=W) (X:=Y) (s:=s) n) :
 HEq (cfg (same.symm ▸ f) n data.2)
 (cfg f n (same ▸ data : Packet (W:=W) (X:=Z) (s:=s) n).2) := by
 cases same; rfl

end Transport
variable (factory : Factory W X s)
variable (initial : M.Frame (Value:=W) (Var:=X) (sort:=s))
variable (firstCfg : A.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
variable (language : firstCfg.LowVar=X)
def tailData (n : Nat) : Packet (W:=W) (X:=X) (s:=s) (n+1) :=
 Nat.rec (language ▸ (⟨Lower.Stock.receiver initial firstCfg language,Lower.Stock.seed initial firstCfg language⟩ :
  Packet (W:=W) (X:=firstCfg.LowVar) (s:=s) 1))
  (fun n previous => step factory (n+1) previous) n

def frameAt : (n : Nat) → M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s)
 | 0 => initial
 | n+1 => (tailData factory initial firstCfg language n).1
def cfgAt : (n : Nat) → A.Programme (PhysicalValue:=Lower.Value W n) (PhysicalVar:=X) (sort:=s)
 | 0 => firstCfg
 | n+1 => cfg factory (n+1) (tailData factory initial firstCfg language n).2
theorem languageAt (n : Nat) : (cfgAt factory initial firstCfg language n).LowVar=X := by
 cases n with
 | zero => exact language
 | succ _ => rfl

def scalarAt : (n : Nat) → RootedAccountedUnfolding
 (PresentedRelationEventAt (Expr (PairValue (Lower.Value W n)) (cfgAt factory initial firstCfg language n).LowVar s))
 | 0 => Lower.Stock.scalar initial firstCfg language
 | n+1 => scalar factory (n+1) (tailData factory initial firstCfg language n)
def pairAt : (n : Nat) → RootedAccountedUnfolding
 (PresentedRelationEventAt (Expr (PairValue (PairValue (Lower.Value W n))) (cfgAt factory initial firstCfg language n).LowVar s))
 | 0 => Lower.Stock.pair initial firstCfg language
 | n+1 => pair factory (n+1) (tailData factory initial firstCfg language n)
def receiverAt (n : Nat) := B.initial (frameAt factory initial firstCfg language n) (cfgAt factory initial firstCfg language n)
 (scalarAt factory initial firstCfg language n) (pairAt factory initial firstCfg language n)
def nextCfg : (n : Nat) → A.Programme (PhysicalValue:=PairValue (Lower.Value W n))
 (PhysicalVar:=(cfgAt factory initial firstCfg language n).LowVar) (sort:=s)
 | 0 => cfg (language.symm ▸ factory : Factory W firstCfg.LowVar s) 1 (Lower.Stock.seed initial firstCfg language)
 | n+1 => cfg factory (n+2) (nextSeed factory (n+1) (tailData factory initial firstCfg language n))

theorem receiver_actual (n : Nat) : HEq (receiverAt factory initial firstCfg language n)
 (frameAt factory initial firstCfg language (n+1)) := by
 cases n with
 | zero => exact Transport.frame_heq language 1 ⟨Lower.Stock.receiver initial firstCfg language,Lower.Stock.seed initial firstCfg language⟩
 | succ _ => rfl

theorem next_programme_actual (n : Nat) : HEq (nextCfg factory initial firstCfg language n)
 (cfgAt factory initial firstCfg language (n+1)) := by
 cases n with
 | zero => exact Transport.programme_heq language factory 1 ⟨Lower.Stock.receiver initial firstCfg language,Lower.Stock.seed initial firstCfg language⟩
 | succ _ => rfl

theorem next_scalar_inventory (n : Nat) :
 (frameAt factory initial firstCfg language (n+2)).inventory=some (scalarAt factory initial firstCfg language (n+1)) := rfl

theorem next_pair_inventory (n : Nat) :
 (frameAt factory initial firstCfg language (n+2)).pairInventory=some (pairAt factory initial firstCfg language (n+1)) := rfl

theorem stock_growth (n : Nat) : Lower.Stock.size (frameAt factory initial firstCfg language n)<Lower.Stock.size (frameAt factory initial firstCfg language (n+1)) := by
 have grows : Lower.Stock.size (frameAt factory initial firstCfg language n)<(scalarAt factory initial firstCfg language n).trace.length := by
  cases n with
  | zero => exact Lower.Stock.scalar_growth initial firstCfg language
  | succ n => exact scalar_grows factory (n+1) (tailData factory initial firstCfg language n)
 have sameSize : Lower.Stock.size (receiverAt factory initial firstCfg language n)=Lower.Stock.size (frameAt factory initial firstCfg language (n+1)) := by
  cases n with
  | zero => exact Transport.size_eq language 1 ⟨Lower.Stock.receiver initial firstCfg language,Lower.Stock.seed initial firstCfg language⟩
  | succ _ => rfl
 rw [←sameSize]
 exact grows

theorem stock_strictMono : StrictMono (fun n => Lower.Stock.size (frameAt factory initial firstCfg language n)) :=
 strictMono_nat_of_lt_succ (stock_growth factory initial firstCfg language)
end Lower.SourceFamily
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
