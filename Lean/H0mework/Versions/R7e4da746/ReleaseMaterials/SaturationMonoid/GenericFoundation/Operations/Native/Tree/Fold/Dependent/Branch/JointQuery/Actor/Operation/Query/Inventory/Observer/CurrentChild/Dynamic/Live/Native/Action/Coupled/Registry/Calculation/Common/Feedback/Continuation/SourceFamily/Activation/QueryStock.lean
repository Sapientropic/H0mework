import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Activation.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource.QueryStock
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace Map
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock
 (mapped_trace)
end Map
private theorem preserve_generated {α:Type u} (prior:Option (RootedAccountedUnfolding α))
 (stock:RootedAccountedUnfolding α) : ∀ event∈stock.trace,event∈(T.preserve prior stock).trace := by
 cases prior with
 | none => exact fun _ belongs=>belongs
 | some carried => exact (SourceHistoryCommon.parallel_right _ _ _).1

variable {Sorts:Type u} {W X:Sorts→Type u} [∀ target,AddCommGroup (W target)] {s:Sorts}
local instance lawGroups (n:Nat) (target:Sorts) : AddCommGroup (Lower.Value W n target) := Lower.groups W n target
variable (factory:SF.Factory W X s) (n:Nat) (data:SF.Packet (W:=W) (X:=X) (s:=s) n)
variable (sourceCfg:A.Programme (PhysicalValue:=Lower.Value W n) (PhysicalVar:=X) (sort:=s))
variable (language:sourceCfg.LowVar=X)

abbrev legacyStock := T.preserve (language.symm ▸ factory.extraScalar n data.2 data.1)
 (Lower.Stock.scalar data.1 sourceCfg language)

private theorem cast_none {Y Z:Sorts→Type u} (same:Y=Z) :
 (same ▸ (none:Option (RootedAccountedUnfolding (PresentedRelationEventAt
  (Expr (PairValue (Lower.Value W n)) Y s)))))=none := by
 cases same
 rfl

/-- Both old scalar components remain present, for every configured output. -/
theorem scalar_legacy_preserved : ∀ event∈(legacyStock factory n data sourceCfg language).trace,
 event∈(scalar factory n data sourceCfg language).trace := by
 intro event belongs
 exact preserve_generated _ _ event (preserve_generated _ _ event belongs)

/-- The exact configured query stock enters the admission scalar without changing its syntax. -/
theorem scalar_query_stock
 (stock:RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue (Lower.Value W n)) X s)))
 (written:sourceCfg.nextPairInventory data.1=some stock) (event) (belongs:event∈stock.trace) :
 (language.symm ▸ event)∈(scalar factory n data sourceCfg language).trace := by
 unfold scalar
 rw [written,Lower.Stock.cast_some]
 exact (SourceHistoryCommon.parallel_left _ _ _).1 _ ((Lower.Stock.cast_mem language.symm stock event).mpr belongs)

/-- The configured physical stock keeps every event under the existing physical-to-pair lift. -/
theorem scalar_physical_stock
 (stock:RootedAccountedUnfolding (PresentedRelationEventAt (Expr (Lower.Value W n) X s)))
 (written:sourceCfg.nextInventory data.1=some stock) (event) (belongs:event∈stock.trace) :
 (language.symm ▸ T.liftEvent event)∈(scalar factory n data sourceCfg language).trace := by
 unfold scalar
 apply preserve_generated
 rw [written,Option.map_some,Lower.Stock.cast_some]
 apply (SourceHistoryCommon.parallel_left _ _ _).1
 apply (Lower.Stock.cast_mem language.symm (stock.map T.liftEvent) (T.liftEvent event)).mpr
 rw [Map.mapped_trace]
 exact List.mem_map_of_mem belongs

/-- The real next seed consumes the same entire configured query receipt. -/
theorem next_seed_query_stock
 (stock:RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue (Lower.Value W n)) X s)))
 (written:sourceCfg.nextPairInventory data.1=some stock) (event) (belongs:event∈stock.trace) :
 (language.symm ▸ event)∈(nextSeed factory n data sourceCfg language).trace :=
 (SourceHistoryCommon.parallel_left _ _ _).1 _
  (scalar_query_stock factory n data sourceCfg language stock written event belongs)

theorem next_seed_physical_stock
 (stock:RootedAccountedUnfolding (PresentedRelationEventAt (Expr (Lower.Value W n) X s)))
 (written:sourceCfg.nextInventory data.1=some stock) (event) (belongs:event∈stock.trace) :
 (language.symm ▸ T.liftEvent event)∈(nextSeed factory n data sourceCfg language).trace :=
 (SourceHistoryCommon.parallel_left _ _ _).1 _
  (scalar_physical_stock factory n data sourceCfg language stock written event belongs)

/-- Explicit empty configured outputs recover the previous scalar producer, including its extras. -/
theorem scalar_no_configured_stock
 (physical:sourceCfg.nextInventory data.1=none) (query:sourceCfg.nextPairInventory data.1=none) :
 scalar factory n data sourceCfg language=legacyStock factory n data sourceCfg language := by
 simp only [scalar,legacyStock,physical,query,Option.map_none,cast_none,T.preserve]

/-- A query receipt is retained as a complete rooted history, independently of the physical output. -/
theorem scalar_some_query_stock
 (stock:RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue (Lower.Value W n)) X s)))
 (written:sourceCfg.nextPairInventory data.1=some stock) :
 scalar factory n data sourceCfg language=SourceHistoryCommon.seed (language.symm ▸ stock)
  (T.preserve (language.symm ▸ (sourceCfg.nextInventory data.1).map (fun history=>history.map T.liftEvent))
   (legacyStock factory n data sourceCfg language)) := by
 unfold scalar
 rw [written,Lower.Stock.cast_some]
 rfl

/-- A physical receipt enters as its complete mapped history; no query receipt is required. -/
theorem scalar_some_physical_stock
 (stock:RootedAccountedUnfolding (PresentedRelationEventAt (Expr (Lower.Value W n) X s)))
 (written:sourceCfg.nextInventory data.1=some stock) :
 scalar factory n data sourceCfg language=T.preserve (language.symm ▸ sourceCfg.nextPairInventory data.1)
  (SourceHistoryCommon.seed (language.symm ▸ stock.map T.liftEvent)
   (legacyStock factory n data sourceCfg language)) := by
 unfold scalar
 rw [written,Option.map_some,Lower.Stock.cast_some]
 rfl

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource.QueryStock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
