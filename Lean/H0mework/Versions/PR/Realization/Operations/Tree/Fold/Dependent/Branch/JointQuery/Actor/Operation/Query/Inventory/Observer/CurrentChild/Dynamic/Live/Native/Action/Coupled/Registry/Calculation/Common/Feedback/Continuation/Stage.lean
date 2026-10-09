import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Stage
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
namespace Lower
variable {S : Type u} (W : S → Type u) [∀ s,AddCommGroup (W s)]
local instance carriedStageGroup (n : Nat) (s : S) : AddCommGroup (Value W n s) := groups W n s
variable {W} {X : S → Type u} {s : S}
namespace Transport
variable {Y Z : S → Type u}
abbrev Data (Y : S → Type u) := M.Frame (Value:=PairValue W) (Var:=Y) (sort:=s) ×
 RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue W) Y s))
theorem frame_heq (same : Y=Z) (data : Data (W:=W) (s:=s) Y) : HEq data.1 (same ▸ data : Data (W:=W) (s:=s) Z).1 := by
 cases same; rfl

theorem programme_heq (same : Y=Z) (data : Data (W:=W) (s:=s) Y) :
 HEq (R.programme data.2) (R.programme (same ▸ data : Data (W:=W) (s:=s) Z).2) := by
 cases same; rfl

theorem size_eq (same : Y=Z) (data : Data (W:=W) (s:=s) Y) :
 Stock.size data.1=Stock.size (same ▸ data : Data (W:=W) (s:=s) Z).1 := by
 cases same; rfl

theorem registry_current_eq (same : Y=Z) (data : Data (W:=W) (s:=s) Y) :
 (Base.presentation data.1 (R.programme data.2)).erase=
 (Base.presentation (same ▸ data : Data (W:=W) (s:=s) Z).1
   (R.programme (same ▸ data : Data (W:=W) (s:=s) Z).2)).erase := by
 cases same; rfl
end Transport
variable (initial : M.Frame (Value:=W) (Var:=X) (sort:=s))
variable (firstCfg : A.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
variable (language : firstCfg.LowVar=X)
abbrev TailData (n : Nat) :=
 M.Frame (Value:=Value W (n+1)) (Var:=X) (sort:=s) ×
 RootedAccountedUnfolding (PresentedRelationEventAt (Expr (Value W (n+1)) X s))
abbrev tailData := SourceFamily.tailData (SourceFamily.defaultFactory W X s) initial firstCfg language
abbrev frameAt := SourceFamily.frameAt (SourceFamily.defaultFactory W X s) initial firstCfg language
def nativeCfgAt : (n : Nat) → A.Programme (PhysicalValue:=Value W n) (PhysicalVar:=X) (sort:=s)
 | 0 => firstCfg
 | n+1 => R.nativeProgramme (tailData initial firstCfg language n).2
abbrev cfgAt := SourceFamily.cfgAt (SourceFamily.defaultFactory W X s) initial firstCfg language
theorem languageAt (n : Nat) : (cfgAt initial firstCfg language n).LowVar=X :=
 SourceFamily.languageAt (SourceFamily.defaultFactory W X s) initial firstCfg language n
abbrev scalarAt := SourceFamily.scalarAt (SourceFamily.defaultFactory W X s) initial firstCfg language
abbrev pairAt := SourceFamily.pairAt (SourceFamily.defaultFactory W X s) initial firstCfg language
abbrev nextCfg := SourceFamily.nextCfg (SourceFamily.defaultFactory W X s) initial firstCfg language
def generated (n : Nat) := B.generatedAction (frameAt initial firstCfg language n) (cfgAt initial firstCfg language n)
 (scalarAt initial firstCfg language n) (pairAt initial firstCfg language n) (nextCfg initial firstCfg language n)
def presentationAt (n : Nat) := B.presentation (frameAt initial firstCfg language n) (cfgAt initial firstCfg language n)
 (scalarAt initial firstCfg language n) (pairAt initial firstCfg language n) (nextCfg initial firstCfg language n)
def queryAt (n : Nat) := B.query (frameAt initial firstCfg language n) (cfgAt initial firstCfg language n)

theorem receiver_actual (n : Nat) : HEq
 (Stock.receiver (frameAt initial firstCfg language n) (cfgAt initial firstCfg language n) (languageAt initial firstCfg language n))
 (frameAt initial firstCfg language (n+1)) := by
 cases n <;> exact SourceFamily.receiver_actual (SourceFamily.defaultFactory W X s) initial firstCfg language _

theorem next_programme_actual (n : Nat) : HEq (nextCfg initial firstCfg language n) (cfgAt initial firstCfg language (n+1)) := SourceFamily.next_programme_actual (SourceFamily.defaultFactory W X s) initial firstCfg language n

theorem generated_target_root (n : Nat) : type_of% (B.target_root (frameAt initial firstCfg language n) (cfgAt initial firstCfg language n)
 (scalarAt initial firstCfg language n) (pairAt initial firstCfg language n) (nextCfg initial firstCfg language n)
 (B.sourceEvent (frameAt initial firstCfg language n) (cfgAt initial firstCfg language n))) := B.target_root _ _ _ _ _ _

theorem own_canonical_next (n : Nat) : type_of% (B.target_erasure (frameAt initial firstCfg language n) (cfgAt initial firstCfg language n)
 (scalarAt initial firstCfg language n) (pairAt initial firstCfg language n) (nextCfg initial firstCfg language n)) := B.target_erasure _ _ _ _ _

theorem stock_growth (n : Nat) : Stock.size (frameAt initial firstCfg language n)<Stock.size (frameAt initial firstCfg language (n+1)) :=
 SourceFamily.stock_growth (SourceFamily.defaultFactory W X s) initial firstCfg language n

theorem stock_strictMono : StrictMono (fun n => Stock.size (frameAt initial firstCfg language n)) :=
 SourceFamily.stock_strictMono (SourceFamily.defaultFactory W X s) initial firstCfg language

theorem whole_first (n : Nat) : type_of% (generated initial firstCfg language n).target.firstDestination_heq :=
 (generated initial firstCfg language n).target.firstDestination_heq

theorem inherited (n : Nat) (projection : (B.sourceRoot (frameAt initial firstCfg language n) (cfgAt initial firstCfg language n)).toAuthoritativeRoot.source.projectionLaw.Projection) :
 type_of% ((generated initial firstCfg language n).target.oldOutcome_heq projection) := (generated initial firstCfg language n).target.oldOutcome_heq projection
end Lower
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
